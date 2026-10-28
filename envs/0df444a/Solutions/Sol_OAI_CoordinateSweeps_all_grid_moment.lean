-- Prove2me | solution 1 for OAI.CoordinateSweeps.all_grid_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:32:09.28056+00:00
-- url     : https://prove2.me/submissions/ff2221b8-5614-436a-a322-5b77014218de

import Mathlib
import Definitions.Def_CoordinateSweeps
import Definitions.Def_OAIQ56Cs000
import Theorems.Thm_OAI_CoordinateSweeps_Grid_Holes_conditional_sparse_main

section
-- module Solutions.OAIQ56_CS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
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

theorem choiceWeight_pos (G : Grid) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (ω : G.Choices) : 0 < G.choiceWeight z ω := by
  apply Finset.prod_pos
  intro j _
  apply Finset.prod_pos
  intro L _
  apply add_pos_of_pos_of_nonneg
  · apply mul_pos (sub_pos.mpr hz')
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact mul_nonneg hz ((binaryLaw (G.bits j)).nonneg (ω j L))

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
namespace CoordinateSweeps.PositiveTensor

variable {J : Type*} [Fintype J] [DecidableEq J]

/- Finite positive operators are dominated by their trace times identity. -/
theorem trace_domination (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    (Matrix.trace A • (1 : Matrix J J ℂ) - A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let d : J → ℂ := RCLike.ofReal ∘ hA.isHermitian.eigenvalues
  have ht : Matrix.trace A = ∑ i, d i := hA.isHermitian.trace_eq_sum_eigenvalues
  have hd (i : J) : 0 ≤ Matrix.trace A - d i := by
    rw [ht, sub_nonneg]
    exact Finset.single_le_sum (fun j _ => by
      change (0 : ℂ) ≤ (hA.isHermitian.eigenvalues j : ℂ)
      exact_mod_cast hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hD : (Matrix.diagonal (fun i => Matrix.trace A - d i)).PosSemidef := Matrix.PosSemidef.diagonal hd
  have h := hD.mul_mul_conjTranspose_same (U : Matrix J J ℂ)
  have hU : (U : Matrix J J ℂ) * (U : Matrix J J ℂ).conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hspec : (U : Matrix J J ℂ) * Matrix.diagonal d *
      (U : Matrix J J ℂ).conjTranspose = A := by
    simpa only [U,d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hA.isHermitian.spectral_theorem.symm
  have he : (Matrix.diagonal (fun i => Matrix.trace A - d i)) =
      Matrix.trace A • (1 : Matrix J J ℂ) - Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [he, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, hspec] at h
  exact h

/- A positive operator supported on an orthogonal projection is dominated
by the same trace times that projection, with no ambient-dimension loss. -/
theorem projection_trace_domination (A P : Matrix J J ℂ) (hA : A.PosSemidef)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hPA : P*A=A) :
    (Matrix.trace A • P - A).PosSemidef := by
  have h := (trace_domination A hA).mul_mul_conjTranspose_same P
  have hAP : A*P=A := by
    have hh := congrArg Matrix.conjTranspose hPA
    simpa only [Matrix.conjTranspose_mul,hA.isHermitian.eq,hP.eq] using hh
  simpa only [hP.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hP2, hPA, hAP] using h

variable {K : Type*} [Fintype K] [DecidableEq K]

omit [DecidableEq J] in
theorem outer_sum_domination (v : K → J → ℂ) :
    ((Fintype.card K : ℂ) • (∑ k, outer (v k)) - outer (∑ k, v k)).PosSemidef := by
  let B : Matrix J K ℂ := fun j k => v k j
  let e : K → ℂ := fun _ => 1
  have h := trace_domination (outer e) (Matrix.posSemidef_vecMulVec_self_star e)
  have ht : Matrix.trace (outer e) = (Fintype.card K : ℂ) := by simp [Matrix.trace, outer, e, Matrix.vecMulVec]
  rw [ht] at h
  have hc := h.mul_mul_conjTranspose_same B
  have hBB : B*B.conjTranspose = ∑ k, outer (v k) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.sum_apply]
    rfl
  have hBe : B*outer e*B.conjTranspose = outer (∑ k, v k) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, outer, Matrix.vecMulVec_apply,
      Pi.star_apply]
    simp only [B, e, star_one, mul_one, Finset.sum_apply, star_sum]
    rw [← Finset.mul_sum]
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hBB, hBe] using hc

/- The literal finite partial trace; it is a sum of positive submatrices. -/

omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_posSemidef (A : Matrix (J × K) (J × K) ℂ) (hA : A.PosSemidef) :
    (partialTrace A).PosSemidef := by
  have he : partialTrace A = ∑ k, A.submatrix (fun i => (i,k)) (fun i => (i,k)) := by
    ext i j
    simp [partialTrace, Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun k _ => hA.submatrix _)

omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_outer_matrix (A : Matrix J K ℂ) :
    partialTrace (outer (fun x : J × K => A x.1 x.2)) = A*A.conjTranspose := by
  ext i j
  simp [partialTrace, outer, Matrix.vecMulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
end CoordinateSweeps.PositiveTensor
namespace CoordinateSweeps.PositiveTensor
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma productMatrix_mul (r t : I → Matrix A A ℂ) :
    productMatrix (fun i => r i * t i) = productMatrix r * productMatrix t := by
  ext u w
  simp only [productMatrix,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact Finset.prod_mul_distrib

omit [DecidableEq I] [Fintype A] [DecidableEq A] in
lemma productMatrix_star (r : I → Matrix A A ℂ) :
    productMatrix (fun i => (r i).conjTranspose) = (productMatrix r).conjTranspose := by
  ext u w
  simp [productMatrix,Matrix.conjTranspose_apply]

omit [DecidableEq I] [Fintype A] [DecidableEq A] in
lemma productMatrix_smul (c : I → ℂ) (r : I → Matrix A A ℂ) :
    productMatrix (fun i => c i • r i) = (∏ i, c i) • productMatrix r := by
  ext u w
  simp only [productMatrix,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

lemma productMatrix_posSemidef (r : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef) :
    (productMatrix r).PosSemidef := by
  have h (i : I) : ∃ b : Matrix A A ℂ, r i = b.conjTranspose*b := by
    simpa only [Matrix.star_eq_conjTranspose] using
      CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hr i).nonneg
  choose b hb using h
  rw [show r = (fun i => (b i).conjTranspose*b i) from funext hb]
  rw [productMatrix_mul,productMatrix_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype A] [DecidableEq A] in
lemma productMatrix_sum {K : Type*} [Fintype K] (r : I → K → Matrix A A ℂ) :
    productMatrix (fun i => ∑ k, r i k) = ∑ w : I → K, productMatrix (fun i => r i (w i)) := by
  ext u v
  simp only [productMatrix,Matrix.sum_apply]
  exact Fintype.prod_sum (fun i k => r i k (u i) (v i))

lemma productMatrix_mono (r t : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef)
    (ht : ∀ i, (t i - r i).PosSemidef) :
    (productMatrix t - productMatrix r).PosSemidef := by
  let f : I → Bool → Matrix A A ℂ := fun i b => if b then t i-r i else r i
  have hsum (i : I) : ∑ b : Bool, f i b = t i := by
    simp [f]
  have he : productMatrix r = productMatrix (fun i => f i (false)) := by simp [f]
  rw [he,show t = (fun i => ∑ b : Bool, f i b) from (funext hsum).symm,productMatrix_sum]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (fun _ : I => false)),add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro w _
  apply productMatrix_posSemidef
  intro i
  cases w i <;> simp only [f,Bool.false_eq_true,↓reduceIte]
  · exact hr i
  · exact ht i

omit [DecidableEq A] in
lemma pair_product_partialTrace (z : I → Matrix A A ℂ) (u v : I → A) :
    (∑ w : I → A, (∏ i, z i (u i) (w i)) * star (∏ i, z i (v i) (w i))) =
      productMatrix (fun i => z i*(z i).conjTranspose) u v := by
  simp only [productMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,star_prod]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => z i (u i) a * star (z i (v i) a))).symm
end CoordinateSweeps.PositiveTensor

namespace CoordinateSweeps.PositiveTensor
variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

omit [Fintype J] in
lemma inclusion_mulVec_image (e : K ↪ J) (v : K → ℂ) (k : K) :
    (inclusion e).mulVec v (e k) = v k := by
  simp [Matrix.mulVec,dotProduct,inclusion,e.injective.eq_iff]

omit [Fintype J] [DecidableEq K] in
lemma inclusion_mulVec_notin (e : K ↪ J) (v : K → ℂ) (j : J)
    (hj : j ∉ Set.range e) : (inclusion e).mulVec v j = 0 := by
  have hne (k : K) : j ≠ e k := fun he => hj ⟨k,he.symm⟩
  simp [Matrix.mulVec,dotProduct,inclusion,hne]

omit [Fintype K] in
lemma inclusion_isometry (e : K ↪ J) : (inclusion e).conjTranspose * inclusion e = 1 := by
  ext k k'
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,inclusion]
  rw [Finset.sum_eq_single (e k)]
  · by_cases h : k=k' <;> simp [h,e.injective.eq_iff,Matrix.one_apply]
  · intro j _ hj
    simp [hj]
  · simp

omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma mul_outer_mul_star (B : Matrix J K ℂ) (v : K → ℂ) :
    B * Matrix.vecMulVec v (star v) * B.conjTranspose =
      Matrix.vecMulVec (B.mulVec v) (star (B.mulVec v)) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.vecMulVec_apply,Matrix.conjTranspose_apply,
    Pi.star_apply,Matrix.mulVec,dotProduct,star_sum,star_mul]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma inclusion_trace_outer (e : K ↪ J) (v : K → ℂ) :
    Matrix.trace (Matrix.vecMulVec ((inclusion e).mulVec v) (star ((inclusion e).mulVec v))) =
      Matrix.trace (Matrix.vecMulVec v (star v)) := by
  rw [← mul_outer_mul_star,Matrix.trace_mul_cycle,inclusion_isometry,Matrix.one_mul]
end CoordinateSweeps.PositiveTensor
namespace CoordinateSweeps.PositiveTensor
variable {J K L : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype L]
omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_sub (A B : Matrix (J × K) (J × K) ℂ) :
    partialTrace (A-B) = partialTrace A-partialTrace B := by
  ext i j
  simp [partialTrace,Finset.sum_sub_distrib]
omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_smul (c : ℂ) (A : Matrix (J × K) (J × K) ℂ) :
    partialTrace (c • A) = c • partialTrace A := by
  ext i j
  simp [partialTrace,Matrix.smul_apply,Finset.mul_sum]
omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_sum (A : L → Matrix (J × K) (J × K) ℂ) :
    partialTrace (∑ k, A k) = ∑ k, partialTrace (A k) := by
  ext i j
  simp only [partialTrace,Matrix.sum_apply]
  exact Finset.sum_comm
end CoordinateSweeps.PositiveTensor
namespace CoordinateSweeps.PositiveTensor
variable {J : Type*} [Fintype J] [DecidableEq J]
omit [Fintype J] [DecidableEq J] in
lemma domination_pad (A B : Matrix J J ℂ) (a b : ℂ) (hB : B.PosSemidef) (hab : a ≤ b)
    (h : (a • B-A).PosSemidef) : (b • B-A).PosSemidef := by
  have hh := (hB.smul (sub_nonneg.mpr hab)).add h
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  module
omit [Fintype J] [DecidableEq J] in
lemma domination_trans (A B C : Matrix J J ℂ) (a b : ℂ) (ha : 0 ≤ a)
    (hAB : (a • B-A).PosSemidef) (hBC : (b • C-B).PosSemidef) :
    ((a*b) • C-A).PosSemidef := by
  have h := (hBC.smul ha).add hAB
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  module
end CoordinateSweeps.PositiveTensor
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CoordinateSweeps.DependentTensor
variable {I : Type*} [Fintype I] [DecidableEq I] {J : I → Type*}
  [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

omit [∀ index, DecidableEq (J index)] in
lemma tensor_mul (A B : ∀ i, Matrix (J i) (J i) ℂ) :
    tensor (fun i => A i*B i)=tensor A*tensor B := by
  ext x y
  simp only [tensor,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

omit [DecidableEq I] [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_star (A : ∀ i, Matrix (J i) (J i) ℂ) :
    tensor (fun i => (A i).conjTranspose)=(tensor A).conjTranspose := by
  ext x y
  simp [tensor,Matrix.conjTranspose_apply]

omit [∀ index, DecidableEq (J index)] in
lemma tensor_trace (A : ∀ i, Matrix (J i) (J i) ℂ) :
    Matrix.trace (tensor A)=∏ i, Matrix.trace (A i) := by
  simp only [Matrix.trace,Matrix.diag,tensor]
  exact (Fintype.prod_sum (fun i => fun j : J i => A i j j)).symm

omit [DecidableEq I] [∀ index, Fintype (J index)] in
lemma tensor_one : tensor (fun i => (1 : Matrix (J i) (J i) ℂ))=1 := by
  classical
  ext x y
  by_cases h : x=y
  · subst y; simp [tensor]
  · obtain ⟨i,hi⟩:=Function.ne_iff.mp h
    simp only [tensor,Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

lemma tensor_pow (A : ∀ i, Matrix (J i) (J i) ℂ) (q : ℕ) :
    tensor (fun i => A i^q)=(tensor A)^q := by
  induction q with
  | zero => simpa using tensor_one
  | succ q ih => simp only [pow_succ,tensor_mul,ih]

lemma tensor_moment (A : ∀ i, Matrix (J i) (J i) ℂ) (q : ℕ) :
    Matrix.trace (((tensor A).conjTranspose*tensor A)^q)=
      ∏ i, Matrix.trace (((A i).conjTranspose*A i)^q) := by
  rw [← tensor_star,← tensor_mul,← tensor_pow,tensor_trace]

open scoped MatrixOrder in
lemma tensor_posSemidef (A : ∀ i, Matrix (J i) (J i) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensor A).PosSemidef := by
  choose B hB using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA i).nonneg
  have he : A=fun i => (B i).conjTranspose*B i := by funext i; exact hB i
  rw [he,tensor_mul,tensor_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq I] [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_smul (c : I → ℂ) (A : ∀ i, Matrix (J i) (J i) ℂ) :
    tensor (fun i => c i • A i)=(∏ i, c i) • tensor A := by
  ext x y
  simp only [tensor,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

omit [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_sum {K : I → Type*} [∀ i, Fintype (K i)]
    (A : ∀ i, K i → Matrix (J i) (J i) ℂ) :
    tensor (fun i => ∑ k, A i k)=∑ x : ∀ i, K i, tensor (fun i => A i (x i)) := by
  ext a b
  simp only [tensor,Matrix.sum_apply]
  exact Fintype.prod_sum _

/- Tensor positivity is monotone in every factor simultaneously. -/
lemma tensor_mono (A B : ∀ i, Matrix (J i) (J i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hAB : ∀ i, (B i-A i).PosSemidef) :
    (tensor B-tensor A).PosSemidef := by
  classical
  let F (i : I) (b : Bool) := if b then B i-A i else A i
  have he : B=(fun i => ∑ b : Bool, F i b) := by
    funext i
    simp [F]
  have ht : tensor B=∑ x : I → Bool, tensor (fun i => F i (x i)) := by
    rw [he,tensor_sum]
  have hzero : tensor (fun i => F i ((fun _ => false) i))=tensor A := by simp [F]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (I → Bool))
    (fun x => tensor (fun i => F i (x i))) (Finset.mem_univ (fun _ => false))
  rw [hzero,← ht] at hs
  have hdiff : tensor B-tensor A =
      ∑ x ∈ Finset.univ.erase (fun _ : I => false), tensor (fun i => F i (x i)) := by
    exact (eq_sub_of_add_eq hs).symm
  rw [hdiff]
  apply Matrix.posSemidef_sum
  intro x hx
  apply tensor_posSemidef
  intro i
  dsimp [F]
  split_ifs
  · exact hAB i
  · exact hA i

/- Exact finite mixtures can be tensored without losing normalization. -/
omit [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_mixture {K : I → Type*} [∀ i, Fintype (K i)]
    (w : ∀ i, K i → ℂ) (A : ∀ i, K i → Matrix (J i) (J i) ℂ) :
    tensor (fun i => ∑ k, w i k • A i k)=
      ∑ x : ∀ i, K i, (∏ i, w i (x i)) • tensor (fun i => A i (x i)) := by
  rw [tensor_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact tensor_smul _ _

end CoordinateSweeps.DependentTensor
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.TensorBoard
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma tensor_mul (A B : I → Matrix J J ℂ) :
    tensor (fun i => A i*B i)=tensor A*tensor B := by
  ext x y
  simp only [tensor,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

omit [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma tensor_star (A : I → Matrix J J ℂ) :
    tensor (fun i => (A i).conjTranspose)=(tensor A).conjTranspose := by
  ext x y
  simp [tensor,Matrix.conjTranspose_apply]

omit [DecidableEq J] in
lemma tensor_trace (A : I → Matrix J J ℂ) :
    Matrix.trace (tensor A)=∏ i, Matrix.trace (A i) := by
  simp only [Matrix.trace,Matrix.diag,tensor]
  exact (Fintype.prod_sum (fun i : I => fun j : J => A i j j)).symm

open scoped MatrixOrder in
lemma tensor_posSemidef (A : I → Matrix J J ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensor A).PosSemidef := by
  choose B hB using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA i).nonneg
  have he : A=fun i => (B i).conjTranspose*B i := by
    funext i
    exact hB i
  rw [he,tensor_mul,tensor_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

open scoped MatrixOrder in
lemma trace_mul_nonneg {A B : Matrix J J ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A*B) := by
  obtain ⟨C,rfl⟩:=CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.star_eq_conjTranspose,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

lemma trace_mono_right {A B C : Matrix J J ℂ} (h : (B-A).PosSemidef)
    (hC : C.PosSemidef) : Matrix.trace (A*C) ≤ Matrix.trace (B*C) := by
  have hh:=trace_mul_nonneg h hC
  rw [sub_mul,Matrix.trace_sub] at hh
  exact sub_nonneg.mp hh

/- The source's deleted-site AMGM loss exp(h), using x≤exp(x−1).
This avoids unnecessary equal-size/nonempty column cases. -/
lemma free_product_le_exp {T : Type*} [Fintype T] (F : Finset T) (x : T → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i ≤ Fintype.card T) :
    ∏ i ∈ F, x i ≤ Real.exp (Fintype.card T-F.card) := by
  calc
    _ ≤ ∏ i ∈ F, Real.exp (x i-1) := by
      apply Finset.prod_le_prod (fun index _ => hx index)
      intro i hi
      linarith [Real.add_one_le_exp (x i-1)]
    _ = Real.exp (∑ i ∈ F, (x i-1)) := by rw [Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      rw [Finset.sum_sub_distrib,Finset.sum_const, nsmul_eq_mul,mul_one]
      have hh : ∑ i ∈ F, x i ≤ ∑ i, x i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hx i)
      linarith)

end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

/- Regularization is genuine positive definite, not an inverse assumption. -/
omit [DecidableEq R] [Fintype J] in
lemma average_regularization_posDef (r : R → Matrix J J ℂ)
    (hr : ∀ i, (r i).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (((Fintype.card R : ℂ)⁻¹) • ∑ i, r i) + (ε : ℂ) • (1 : Matrix J J ℂ) |>.PosDef := by
  apply Matrix.PosDef.posSemidef_add
  · exact (Matrix.posSemidef_sum _ (fun i _ => hr i)).smul (by positivity)
  · exact Matrix.PosDef.one.smul (by exact_mod_cast hε : (0 : ℂ) < ε)

omit [DecidableEq R] in
lemma whitening_sum_bound (r : R → Matrix J J ℂ)
    (B A : Matrix J J ℂ) (hA : A.IsHermitian) (hABA : A*B*A=1)
    (hB : (B-((Fintype.card R : ℂ)⁻¹) • ∑ i, r i).PosSemidef) :
    ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef := by
  have h := hB.mul_mul_conjTranspose_same A
  rw [hA.eq,Matrix.mul_sub,Matrix.sub_mul,hABA,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul] at h
  have hh := h.smul (show (0 : ℂ) ≤ Fintype.card R by positivity)
  have hc : (Fintype.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [smul_sub,smul_smul,mul_inv_cancel₀ hc,one_smul] using hh

omit [DecidableEq R] [Nonempty R] in
lemma trace_whitened_sum_le (r : R → Matrix J J ℂ)
    (v A : Matrix J J ℂ) (hv : v.PosSemidef) (ht : Matrix.trace v=1)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    ∑ i, (Matrix.trace (A*r i*A*v)).re ≤ Fintype.card R := by
  have hh:=trace_mono_right hw hv
  simp only [Matrix.sum_mul,Matrix.trace_sum,Matrix.smul_mul,one_mul,Matrix.trace_smul,ht] at hh
  simpa only [Complex.re_sum,smul_eq_mul,mul_one,Complex.natCast_re] using (Complex.le_def.mp hh).1

/- Exact exp(h) loss from deleted sites, with the whitening condition that
will be supplied by the constructed regularized average. -/
omit [Nonempty R] in
theorem board_trace_le (F : Finset (R × C)) (r : R → Matrix J J ℂ)
    (v : C → Matrix J J ℂ) (hr : ∀ i, (r i).PosSemidef)
    (hv : ∀ j, (v j).PosSemidef) (ht : ∀ j, Matrix.trace (v j)=1)
    (A : Matrix J J ℂ) (hA : A.IsHermitian)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    (Matrix.trace (tensor (fun x : F => A*r x.val.1*A) *
      tensor (fun x : F => v x.val.2))).re ≤
        Real.exp (Fintype.card R*Fintype.card C-F.card) := by
  let t (x : R × C) : ℂ := Matrix.trace (A*r x.1*A*v x.2)
  have hn (x : R × C) : 0 ≤ t x := by
    apply trace_mul_nonneg _ (hv x.2)
    simpa only [hA.eq] using (hr x.1).mul_mul_conjTranspose_same A
  have he (x : R × C) : ((t x).re : ℂ)=t x := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp (hn x)).2
  have hs : ∑ x : R × C, (t x).re ≤ Fintype.card (R × C) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    calc
      _ ≤ ∑ _ : C, (Fintype.card R : ℝ) := Finset.sum_le_sum (fun j _ => trace_whitened_sum_le r (v j) A (hv j) (ht j) hw)
      _ = _ := by simp [Fintype.card_prod]; ring
  have hh := free_product_le_exp F (fun x => (t x).re)
    (fun x => (Complex.nonneg_iff.mp (hn x)).1) hs
  rw [← tensor_mul,tensor_trace]
  have hp : (∏ x : F, t x.val).re=∏ x ∈ F, (t x).re := by
    have he' : ∏ x : F, t x.val= (∏ x : F, (t x.val).re : ℝ) := by
      push_cast
      exact Finset.prod_congr rfl (fun x _ => (he x.val).symm)
    calc
      _ = ∏ x : F, (t x.val).re := by simpa only [Complex.ofReal_re] using congrArg Complex.re he'
      _ = _ := Finset.prod_coe_sort F (fun x => (t x).re)
  change (∏ x : F, t x.val).re ≤ _
  rw [hp]
  simpa only [Fintype.card_prod,Nat.cast_mul] using hh

end CoordinateSweeps.TensorBoard
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

theorem trace_moment_nonneg {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (q : ℕ) :
    0 ≤ (Matrix.trace ((A.conjTranspose * A)^q)).re :=
  ((Matrix.posSemidef_conjTranspose_mul_self A).pow q).trace_nonneg.1

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

theorem unitary_average_norm_le {D : ℕ} [NeZero D] {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (A : Ω → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    ‖∑ x, (w x : ℂ) • A x‖ ≤ 1 := by
  calc
    _ ≤ ∑ x, ‖(w x : ℂ) • A x‖ := norm_sum_le _ _
    _ = ∑ x, w x * ‖A x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw x)]
    _ ≤ ∑ x, w x := Finset.sum_le_sum (fun x _ =>
      mul_le_of_le_one_right (hw x) (matrix_unitary_norm_le (A x) (hA x)))
    _ = 1 := hs

/- Ordinary, unnormalized even Schatten moment. For a matrix K this is
Tr((K* K)^q), NOT divided by its dimension. -/
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
theorem character_norm :
    (Fintype.card Γ : ℂ)⁻¹ *
      ∑ g : Γ, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)=1 := by
  let : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero)
  have : Nonempty (Representation.Equiv ρ.asRepresentation ρ.asRepresentation) :=
    ⟨Representation.Equiv.refl _⟩
  have h := Representation.char_orthonormal ρ.asRepresentation ρ.asRepresentation
  rw [ite_eq_left (show Nonempty (Representation.Equiv ρ.asRepresentation ρ.asRepresentation)
    from inferInstance)] at h
  simpa [character_asRepresentation, Nat.card_eq_fintype_card] using h

omit [Fintype Γ] in
lemma matrix_inv (g : Γ) : ρ.matrix g⁻¹=(ρ.matrix g).conjTranspose := by
  calc
    ρ.matrix g⁻¹=1*ρ.matrix g⁻¹ := (one_mul _).symm
    _ = ((ρ.matrix g).conjTranspose*ρ.matrix g)*ρ.matrix g⁻¹ := by rw [ρ.unitary g]
    _ = (ρ.matrix g).conjTranspose := by rw [mul_assoc,← map_mul,mul_inv_cancel,map_one,mul_one]

/- Coefficients of the central isotypic projector, in unnormalized trace
convention. They are derived from an actual irrep, not supplied as character
data satisfying unproved orthogonality equations. -/

lemma coefficient_star (g : Γ) : star (ρ.coefficient g)=ρ.coefficient g⁻¹ := by
  simp only [coefficient,star_mul,star_div₀,star_natCast,inv_inv]
  rw [← Matrix.trace_conjTranspose,← ρ.matrix_inv,inv_inv,mul_comm]

variable {A : Type*} [Semiring A] [Algebra ℂ A]

theorem projector_self : ρ.projector ρ.matrix=1 := by
  obtain ⟨c,hc⟩ := ρ.commuting_scalar (ρ.projector ρ.matrix)
    (fun g => (ρ.projector_commute ρ.matrix g).symm)
  have ht : Matrix.trace (ρ.projector ρ.matrix)=(ρ.dimension : ℂ) := by
    simp only [projector,Matrix.trace_sum,Matrix.trace_smul,coefficient]
    calc
      _ = (ρ.dimension : ℂ)*((Fintype.card Γ : ℂ)⁻¹ *
        ∑ g, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        ring
      _ = _ := by rw [ρ.character_norm,mul_one]
  rw [hc,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at ht
  have hD : (ρ.dimension : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ρ.positive.ne'
  have hcone : c=1 := (mul_right_cancel₀ hD (by simpa using ht))
  simpa [hcone] using hc

lemma coefficient_convolution (k : Γ) :
    ∑ g, ρ.coefficient g * ρ.coefficient (g⁻¹*k)=ρ.coefficient k := by
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        Matrix.trace (ρ.matrix k⁻¹ * ρ.projector ρ.matrix) := by
      simp only [projector,Finset.mul_sum,mul_smul_comm,Matrix.trace_sum,
        Matrix.trace_smul,smul_eq_mul,coefficient,mul_inv_rev,inv_inv,map_mul]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ = _ := by rw [ρ.projector_self,mul_one]; rfl

/- Idempotence in every genuine representation, including absent types. -/
theorem projector_idempotent (τ : Γ →* A) : ρ.projector τ * ρ.projector τ=ρ.projector τ := by
  calc
    _ = ∑ g, ∑ h, (ρ.coefficient g * ρ.coefficient h) • τ (g*h) := by
      change (∑ g, ρ.coefficient g • τ g) * (∑ h, ρ.coefficient h • τ h)=_
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [smul_mul_smul_comm,← map_mul]
    _ = ∑ g, ∑ k, (ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k := by
      apply Finset.sum_congr rfl
      intro g hg
      simpa using Equiv.sum_comp (Equiv.mulLeft g)
        (fun k => (ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k)
    _ = ∑ k, ∑ g, (ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k := Finset.sum_comm
    _ = ∑ k, (∑ g, ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k := by
      simp only [Finset.sum_smul]
    _ = _ := by simp only [projector,coefficient_convolution]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem projector_hermitian (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    (ρ.projector τ).conjTranspose=ρ.projector τ := by
  simp only [projector,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    coefficient_star,hu]
  exact Equiv.sum_comp (Equiv.inv Γ) (fun g => ρ.coefficient g • τ g)

theorem projector_posSemidef (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    (ρ.projector τ).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (ρ.projector τ)
  rwa [ρ.projector_hermitian τ hu,ρ.projector_idempotent] at h

end UnitaryIrrep
end CoordinateSweeps

/- Multiplicity in a unitary matrix representation is controlled by the
commutant dimension, with exact (unnormalized) character conventions. -/
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype Γ] in
lemma matrixRepresentation_character (τ : Γ →* Matrix n n ℂ) (g : Γ) :
    (matrixRepresentation τ).character g=Matrix.trace (τ g) :=
  Matrix.trace_toLin'_eq _

lemma character_sum_multiplicity (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) :
    ∑ g, Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹)=
      (Fintype.card Γ : ℂ) *
        Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
  let : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero)
  have hc := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    ρ.asRepresentation (matrixRepresentation τ)
  simp only [character_asRepresentation,matrixRepresentation_character,
    Nat.card_eq_fintype_card] at hc
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ = (Fintype.card Γ : ℂ) * ((Fintype.card Γ : ℂ)⁻¹ *
        ∑ g, Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹)) := by
      rw [← mul_assoc,mul_inv_cancel₀ hN,one_mul]
    _ = _ := by rw [hc]

lemma sum_trace_norm_sq (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    ∑ g, ‖Matrix.trace (τ g)‖^2=(Fintype.card Γ : ℝ) *
      Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ)) := by
  let : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero)
  have hc := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (matrixRepresentation τ) (matrixRepresentation τ)
  simp only [matrixRepresentation_character,Nat.card_eq_fintype_card] at hc
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcs : ∑ g, Matrix.trace (τ g)*Matrix.trace (τ g⁻¹)=
      (Fintype.card Γ : ℂ)*
        Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ)) := by
    rw [← hc,← mul_assoc,mul_inv_cancel₀ hN,one_mul]
  have hstar (g : Γ) : Matrix.trace (τ g⁻¹)=star (Matrix.trace (τ g)) := by
    rw [← hu,Matrix.trace_conjTranspose]
  simp only [hstar,Complex.star_def,Complex.mul_conj'] at hcs
  exact_mod_cast hcs

lemma irrep_sum_trace_norm_sq (ρ : UnitaryIrrep Γ) :
    ∑ g, ‖Matrix.trace (ρ.matrix g)‖^2=(Fintype.card Γ : ℝ) := by
  have hc := ρ.character_norm
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcs : ∑ g, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)=
      (Fintype.card Γ : ℂ) := by
    calc
      _ = (Fintype.card Γ : ℂ)*((Fintype.card Γ : ℂ)⁻¹ *
        ∑ g, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)) := by
          rw [← mul_assoc,mul_inv_cancel₀ hN,one_mul]
      _ = _ := by rw [hc,mul_one]
  simp only [ρ.matrix_inv,Matrix.trace_conjTranspose,Complex.star_def,Complex.mul_conj'] at hcs
  exact_mod_cast hcs

/- No decomposition/classification hypothesis is needed for this character
Cauchy--Schwarz bound. It applies also to absent types (multiplicity zero). -/
theorem multiplicity_sq_le_commutant (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)))^2 ≤
      Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ)) := by
  let m := Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ))
  let e := Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ))
  have hs : (Fintype.card Γ : ℝ)*(m : ℝ) ≤
      ∑ g, ‖Matrix.trace (τ g)‖*‖Matrix.trace (ρ.matrix g)‖ := by
    have hh := norm_sum_le (Finset.univ : Finset Γ)
      (fun g => Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹))
    rw [ρ.character_sum_multiplicity τ] at hh
    simpa only [norm_mul,Complex.norm_natCast,ρ.matrix_inv,Matrix.trace_conjTranspose,
      norm_star,m] using hh
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Γ)
    (fun g => ‖Matrix.trace (τ g)‖) (fun g => ‖Matrix.trace (ρ.matrix g)‖)
  rw [sum_trace_norm_sq τ hu,ρ.irrep_sum_trace_norm_sq] at hcs
  have hN : (0 : ℝ)<Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs' : ((Fintype.card Γ : ℝ)*(m : ℝ))^2 ≤
      (∑ g, ‖Matrix.trace (τ g)‖*‖Matrix.trace (ρ.matrix g)‖)^2 :=
    pow_le_pow_left₀ (mul_nonneg hN.le hm) hs 2
  have heq : ((m : ℝ)^2)*(Fintype.card Γ : ℝ)^2 ≤
      (e : ℝ)*(Fintype.card Γ : ℝ)^2 := by
    dsimp [e] at ⊢
    nlinarith [hs'.trans hcs]
  have hh := (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp heq
  exact_mod_cast hh

end UnitaryIrrep
end CoordinateSweeps
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
namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]

lemma central_sum_commute {A : Type*} [Semiring A] [Algebra ℂ A]
    (τ : Γ →* A) (f : Γ → ℂ) (hf : ∀ k g, f (k*g*k⁻¹)=f g) (k : Γ) :
    τ k*(∑ g, f g • τ g)=(∑ g, f g • τ g)*τ k := by
  have hcoef (g : Γ) : f (k*(g*k⁻¹))=f g := by simpa only [mul_assoc] using hf k g
  have hh := Equiv.sum_comp (MulAut.conj k).toEquiv (fun g => f g • (τ g*τ k))
  simpa [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    MulAut.conj_apply,hcoef,hf,← map_mul,mul_assoc] using hh

omit [Fintype Γ] in
lemma trace_conj (τ : Γ →* Matrix n n ℂ) (k g : Γ) :
    Matrix.trace (τ (k*g*k⁻¹))=Matrix.trace (τ g) := by
  rw [map_mul,map_mul,Matrix.trace_mul_cycle,← map_mul,inv_mul_cancel,map_one,one_mul]

lemma central_character_operator (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) :
    ∑ g, Matrix.trace (τ g⁻¹) • ρ.matrix g =
      ((Fintype.card Γ : ℂ) * Module.finrank ℂ
        (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) / ρ.dimension) •
          (1 : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) := by
  let S := ∑ g, Matrix.trace (τ g⁻¹) • ρ.matrix g
  have hcomm (k : Γ) : ρ.matrix k*S=S*ρ.matrix k :=
    central_sum_commute ρ.matrix _ (fun k g => by
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using trace_conj τ k g⁻¹) k
  obtain ⟨c,hc⟩ := ρ.commuting_scalar S (fun k => (hcomm k).symm)
  have hs : Matrix.trace S=(Fintype.card Γ : ℂ) * Module.finrank ℂ
        (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
    dsimp [S]
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul,smul_eq_mul]
    have hh := Equiv.sum_comp (Equiv.inv Γ)
      (fun g => Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹))
    simp only [Equiv.inv_apply,inv_inv] at hh
    rw [hh,ρ.character_sum_multiplicity τ]
  rw [hc,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at hs
  have hD : (ρ.dimension : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ρ.positive.ne'
  have hce : c=(Fintype.card Γ : ℂ) * Module.finrank ℂ
        (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) / ρ.dimension :=
    (eq_div_iff hD).mpr hs
  exact hc.trans (congrArg (fun c : ℂ => c • (1 : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ)) hce)

/- Exact projected character, with the genuine Hom-space multiplicity. -/
theorem projector_twisted_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) (k : Γ) :
    Matrix.trace (ρ.projector τ*τ k) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace (ρ.matrix k) := by
  let M : ℂ := Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ))
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hD : (ρ.dimension : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ρ.positive.ne'
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        ∑ g, Matrix.trace (ρ.matrix g⁻¹)*Matrix.trace (τ (g*k)) := by
      simp only [projector,Finset.sum_mul,smul_mul_assoc,Matrix.trace_sum,Matrix.trace_smul,
        smul_eq_mul,coefficient,Finset.mul_sum,map_mul]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        ∑ g, Matrix.trace (τ g⁻¹)*Matrix.trace (ρ.matrix (k*g)) := by
      congr 1
      have hh := Equiv.sum_comp ((Equiv.mulRight k).trans (Equiv.inv Γ))
        (fun g => Matrix.trace (τ g⁻¹)*Matrix.trace (ρ.matrix (k*g)))
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro g hg
      change Matrix.trace (ρ.matrix g⁻¹)*Matrix.trace (τ (g*k)) =
        Matrix.trace (τ ((g*k)⁻¹)⁻¹)*Matrix.trace (ρ.matrix (k*(g*k)⁻¹))
      simp only [inv_inv,mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul]
      ring
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        Matrix.trace (ρ.matrix k*(∑ g, Matrix.trace (τ g⁻¹) • ρ.matrix g)) := by
      simp only [Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,map_mul]
    _ = M*Matrix.trace (ρ.matrix k) := by
      rw [ρ.central_character_operator τ,Matrix.mul_smul,mul_one,Matrix.trace_smul,smul_eq_mul]
      change _*( ((Fintype.card Γ : ℂ)*M/(ρ.dimension : ℂ))*_)=_
      field_simp

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]

/- The projected trace formula applies to actual elements of the group algebra,
not just to individual group elements. -/
theorem projector_lift_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (x : MonoidAlgebra ℂ Γ) :
    Matrix.trace (ρ.projector τ*((MonoidAlgebra.lift ℂ _ Γ) τ x)) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace ((MonoidAlgebra.lift ℂ _ Γ) ρ.matrix x) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa using ρ.projector_twisted_trace τ g
  | add x y hx hy => simp only [map_add,mul_add,Matrix.trace_add,hx,hy]
  | smul c x hx => simp only [map_smul,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,hx]; ring

/- Literal finite averages and their adjoints have the same group-algebra
word in every unitary representation. -/

omit [Fintype Γ] in
lemma lift_averageAlgebra {Ω : Type*} [Fintype Ω] (τ : Γ →* Matrix n n ℂ)
    (w : Ω → ℂ) (g : Ω → Γ) :
    (MonoidAlgebra.lift ℂ _ Γ) τ (averageAlgebra w g)=averageMatrix τ w g := by
  simp only [averageAlgebra,map_sum,MonoidAlgebra.lift_single,averageMatrix]

omit [Fintype Γ] in
lemma averageMatrix_star {Ω : Type*} [Fintype Ω] (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) :
    (averageMatrix τ w g).conjTranspose = averageMatrix τ (fun ω => star (w ω))
      (fun ω => (g ω)⁻¹) := by
  simp only [averageMatrix,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,hu]

/- Exact unnormalized even moment trace on a genuine isotypic component. -/
theorem projected_average_moment {Ω : Type*} [Fintype Ω]
    (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) (q : ℕ) :
    Matrix.trace (ρ.projector τ*((averageMatrix τ w g).conjTranspose*averageMatrix τ w g)^q) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace (((averageMatrix ρ.matrix w g).conjTranspose*averageMatrix ρ.matrix w g)^q) := by
  have hr (k : Γ) : (ρ.matrix k).conjTranspose=ρ.matrix k⁻¹ := (ρ.matrix_inv k).symm
  have hh := ρ.projector_lift_trace τ
    ((averageAlgebra (fun ω => star (w ω)) (fun ω => (g ω)⁻¹)*averageAlgebra w g)^q)
  simpa only [map_pow,map_mul,lift_averageAlgebra,← averageMatrix_star τ hu,
    ← averageMatrix_star ρ.matrix hr] using hh

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]

lemma projector_commute_average {Ω : Type*} [Fintype Ω] (ρ : UnitaryIrrep Γ)
    (τ : Γ →* Matrix n n ℂ) (w : Ω → ℂ) (g : Ω → Γ) :
    ρ.projector τ*averageMatrix τ w g=averageMatrix τ w g*ρ.projector τ := by
  simp only [averageMatrix,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    ρ.projector_commute τ]

open scoped MatrixOrder in
lemma trace_positive_product {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A*B) := by
  obtain ⟨C,rfl⟩:=CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.star_eq_conjTranspose,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

lemma projector_complement_posSemidef (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) : (1-ρ.projector τ).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1-ρ.projector τ)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,ρ.projector_hermitian τ hu]
  simp only [sub_mul,mul_sub,one_mul,mul_one,ρ.projector_idempotent]
  module

/- Genuine occurrence gives a lower bound for the encompassing unnormalized
moment, with its actual Hom multiplicity and no missing dimension factor. -/
theorem multiplicity_moment_le {Ω : Type*} [Fintype Ω]
    (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) (q : ℕ) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℝ) *
      (Matrix.trace (((averageMatrix ρ.matrix w g).conjTranspose*averageMatrix ρ.matrix w g)^q)).re ≤
        (Matrix.trace (((averageMatrix τ w g).conjTranspose*averageMatrix τ w g)^q)).re := by
  have hB := (Matrix.posSemidef_conjTranspose_mul_self (averageMatrix τ w g)).pow q
  have hh := trace_positive_product (ρ.projector_complement_posSemidef τ hu) hB
  rw [sub_mul,one_mul,Matrix.trace_sub,ρ.projected_average_moment τ hu w g q] at hh
  simpa only [Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
    sub_nonneg] using (Complex.nonneg_iff.mp hh).1

/- The Schatten moment of the projected average, rather than merely an
inserted projector in the trace, is exactly the same multiplicity formula. -/
theorem projected_operator_moment {Ω : Type*} [Fintype Ω]
    (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) {q : ℕ} (hq : q ≠ 0) :
    Matrix.trace (((ρ.projector τ*averageMatrix τ w g).conjTranspose*
      (ρ.projector τ*averageMatrix τ w g))^q) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace (((averageMatrix ρ.matrix w g).conjTranspose*averageMatrix ρ.matrix w g)^q) := by
  let P := ρ.projector τ
  let K := averageMatrix τ w g
  have hP2 : P*P=P := ρ.projector_idempotent τ
  have hPK : P*K=K*P := ρ.projector_commute_average τ w g
  have hPs : P.conjTranspose=P := ρ.projector_hermitian τ hu
  have hPa : P*K.conjTranspose=K.conjTranspose*P := by
    have hh := congrArg Matrix.conjTranspose hPK
    simpa only [Matrix.conjTranspose_mul,hPs] using hh.symm
  have he : (P*K).conjTranspose*(P*K)=P*(K.conjTranspose*K) := by
    rw [Matrix.conjTranspose_mul,hPs]
    calc
      _ = K.conjTranspose*(P*P)*K := by noncomm_ring
      _ = P*(K.conjTranspose*K) := by rw [hP2,← hPa,mul_assoc]
  have hc : Commute P (K.conjTranspose*K) := by
    show P*(K.conjTranspose*K)=(K.conjTranspose*K)*P
    rw [← mul_assoc,hPa,mul_assoc,hPK,← mul_assoc]
  change Matrix.trace (((P*K).conjTranspose*(P*K))^q)=_
  rw [he,hc.mul_pow,(show IsIdempotentElem P from hP2).pow_eq hq]
  exact ρ.projected_average_moment τ hu w g q

end CoordinateSweeps.UnitaryIrrep
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace CoordinateSweeps.UnitaryIrrep
variable {G : Type*} [Group G] [Fintype G]

lemma projector_other (ρ σ : UnitaryIrrep G)
    (hne : ¬Nonempty (Representation.Equiv ρ.asRepresentation σ.asRepresentation)) :
    ρ.projector σ.matrix=0 := by
  obtain ⟨c,hc⟩ := σ.commuting_scalar (ρ.projector σ.matrix)
    (fun g => (ρ.projector_commute σ.matrix g).symm)
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  have horth := Representation.char_orthonormal σ.asRepresentation ρ.asRepresentation
  rw [ite_eq_right hne] at horth
  have ht : Matrix.trace (ρ.projector σ.matrix)=0 := by
    simp only [projector,Matrix.trace_sum,Matrix.trace_smul,coefficient]
    calc
      _ = (ρ.dimension : ℂ)*((Fintype.card G : ℂ)⁻¹ *
        ∑ g, Matrix.trace (ρ.matrix g⁻¹)*Matrix.trace (σ.matrix g)) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro g hg; simp only [smul_eq_mul]; ring
      _ = 0 := by
        have hh := horth
        simpa [character_asRepresentation,Nat.card_eq_fintype_card,
          ← Finset.mul_sum,mul_comm] using congrArg (fun z : ℂ => (ρ.dimension : ℂ)*z) hh
  rw [hc,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at ht
  have hc0 : c=0 := (mul_eq_zero.mp ht).resolve_right
    (Nat.cast_ne_zero.mpr σ.positive.ne')
  simpa [hc0] using hc

lemma cross_convolution (ρ σ : UnitaryIrrep G)
    (hne : ¬Nonempty (Representation.Equiv σ.asRepresentation ρ.asRepresentation)) (k : G) :
    ∑ g, ρ.coefficient g*σ.coefficient (g⁻¹*k)=0 := by
  calc
    _ = ((σ.dimension : ℂ)/(Fintype.card G : ℂ)) *
        Matrix.trace (σ.matrix k⁻¹ * ρ.projector σ.matrix) := by
      simp only [projector,Finset.mul_sum,mul_smul_comm,Matrix.trace_sum,
        Matrix.trace_smul,smul_eq_mul,coefficient,mul_inv_rev,inv_inv,map_mul]
      apply Finset.sum_congr rfl; intro g hg; ring
    _ = 0 := by
      rw [projector_other ρ σ (fun ⟨e⟩ => hne ⟨e.symm⟩),mul_zero,Matrix.trace_zero,mul_zero]

lemma projector_orthogonal {A : Type*} [Semiring A] [Algebra ℂ A]
    (ρ σ : UnitaryIrrep G)
    (hne : ¬Nonempty (Representation.Equiv σ.asRepresentation ρ.asRepresentation))
    (τ : G →* A) : ρ.projector τ*σ.projector τ=0 := by
  calc
    _ = ∑ g, ∑ h, (ρ.coefficient g*σ.coefficient h) • τ (g*h) := by
      simp only [projector,Finset.sum_mul,Finset.mul_sum,smul_mul_smul_comm,map_mul]
      exact Finset.sum_comm
    _ = ∑ g, ∑ k, (ρ.coefficient g*σ.coefficient (g⁻¹*k)) • τ k := by
      apply Finset.sum_congr rfl; intro g hg
      simpa using Equiv.sum_comp (Equiv.mulLeft g)
        (fun k => (ρ.coefficient g*σ.coefficient (g⁻¹*k)) • τ k)
    _ = ∑ k, (∑ g, ρ.coefficient g*σ.coefficient (g⁻¹*k)) • τ k := by
      rw [Finset.sum_comm]; simp only [Finset.sum_smul]
    _ = 0 := by simp only [cross_convolution ρ σ hne,zero_smul,Finset.sum_const_zero]

lemma projector_intertwiner {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : UnitaryIrrep G)
    (τ : Representation ℂ G V) (ν : Representation ℂ G W)
    (F : Representation.IntertwiningMap τ ν) (v : V) :
    (ρ.projector ν) (F v)=F ((ρ.projector τ) v) := by
  simp only [projector,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,Representation.IntertwiningMap.isIntertwining]

lemma projector_matrix_asRepresentation (ρ σ : UnitaryIrrep G) :
    ρ.projector σ.asRepresentation=Matrix.toLinAlgEquiv' (ρ.projector σ.matrix) := by
  simp only [projector,map_sum,map_smul]
  rfl

end CoordinateSweeps.UnitaryIrrep
end
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
namespace CoordinateSweeps.Grid

/- Concatenation of the *ordered* coordinate sequences. -/

lemma concat_size (A B : Grid) : (concat A B).size=A.size*B.size := by
  change (∏ j : Fin (A.b+B.b), 2^Fin.addCases A.bits B.bits j)=A.size*B.size
  rw [Fin.prod_univ_add]
  simp [size]

lemma concat_allowed (A B : Grid) (r : ℕ) :
    (concat A B).Allowed r ↔ A.Allowed r ∧ B.Allowed r := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd B.b i),
      fun i => by simpa using h (Fin.natAdd A.b i)⟩
  · rintro ⟨hA,hB⟩ i
    induction i using Fin.addCases with
    | left i => simpa using hA i
    | right i => simpa using hB i

end CoordinateSweeps.Grid

noncomputable section
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid

namespace Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma sum_rowCount : ∑ y, H.rowCount y=h := by
  unfold rowCount
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv H.rowOf)).trans (Fintype.card_fin h)
lemma sum_columnCount : ∑ x, H.columnCount x=h := by
  unfold columnCount
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv H.columnOf)).trans (Fintype.card_fin h)

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

/- The literal real line mass, without changing any conditioning. -/

lemma rawLineWeight_cast {k l : ℕ} (h : k=l) (z : ℝ) (σ : Equiv.Perm (Cube k)) :
    rawLineWeight k z σ=rawLineWeight l z ((Equiv.cast (congrArg Cube h)).permCongr σ) := by
  subst l
  rfl

lemma prefix_weight (A B : Grid) (ω : (concat A B).Choices) (z : ℝ) (i : Fin A.b) :
    (∏ L : (concat A B).Line (Fin.castAdd B.b i),
      rawLineWeight ((concat A B).bits (Fin.castAdd B.b i)) z (ω (Fin.castAdd B.b i) L))=
    ∏ y : B.Slot, ∏ L : A.Line i, rawLineWeight (A.bits i) z (rowChoices A B ω y i L) := by
  rw [← (rowLines A B i).prod_comp]
  rw [Fintype.prod_prod_type,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro L _
  rw [rowChoices_apply]
  exact rawLineWeight_cast (concat_bits_left A B i) z _

lemma suffix_weight (A B : Grid) (ω : (concat A B).Choices) (z : ℝ) (i : Fin B.b) :
    (∏ L : (concat A B).Line (Fin.natAdd A.b i),
      rawLineWeight ((concat A B).bits (Fin.natAdd A.b i)) z (ω (Fin.natAdd A.b i) L))=
    ∏ x : A.Slot, ∏ L : B.Line i, rawLineWeight (B.bits i) z (columnChoices A B ω x i L) := by
  rw [← (columnLines A B i).prod_comp]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro L _
  rw [columnChoices_apply]
  exact rawLineWeight_cast (concat_bits_right A B i) z _

/- Complete independent choice mass factors into literal row and column masses. -/
theorem choiceWeight_split (A B : Grid) (ω : (concat A B).Choices) (z : ℝ) :
    (concat A B).choiceWeight z ω =
      (∏ y : B.Slot, A.choiceWeight z (rowChoices A B ω y))*
      (∏ x : A.Slot, B.choiceWeight z (columnChoices A B ω x)) := by
  have hr (G : Grid) (τ : G.Choices) : G.choiceWeight z τ=
      ∏ i : Fin G.b, ∏ L : G.Line i, rawLineWeight (G.bits i) z (τ i L) := by rfl
  rw [hr]
  erw [Fin.prod_univ_add]
  congr 1
  · trans ∏ i : Fin A.b, ∏ y : B.Slot, ∏ L : A.Line i,
        rawLineWeight (A.bits i) z (rowChoices A B ω y i L)
    · apply Finset.prod_congr rfl
      intro i _
      convert prefix_weight A B ω z i using 1
      all_goals try with_reducible_and_instances rfl
      congr 3
      exact Subsingleton.elim _ _
    · rw [Finset.prod_comm]
      rfl
  · trans ∏ i : Fin B.b, ∏ x : A.Slot, ∏ L : B.Line i,
        rawLineWeight (B.bits i) z (columnChoices A B ω x i L)
    · apply Finset.prod_congr rfl
      intro i _
      convert suffix_weight A B ω z i using 1
      all_goals try with_reducible_and_instances rfl
      congr 3
      exact Subsingleton.elim _ _
    · rw [Finset.prod_comm]
      rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma splitCompatibleChoices_weight (z : ℝ)
    (τ : (∀ y : B.Slot, {τ : A.Choices // (H.rowHoles y).Compatible τ}) ×
      (∀ x : A.Slot, {τ : B.Choices // (H.columnHoles x).Compatible τ})) :
    (concat A B).choiceWeight z (H.splitCompatibleChoices.symm τ).val=
      (∏ y, A.choiceWeight z (τ.1 y).val)*(∏ x, B.choiceWeight z (τ.2 x).val) := by
  rw [choiceWeight_split]
  have hr (y : B.Slot) : rowChoices A B (H.splitCompatibleChoices.symm τ).val y=(τ.1 y).val := by
    change (choicesSplit A B ((choicesSplit A B).symm _)).1 y=_
    rw [Equiv.apply_symm_apply]
  have hc (x : A.Slot) : columnChoices A B (H.splitCompatibleChoices.symm τ).val x=(τ.2 x).val := by
    change (choicesSplit A B ((choicesSplit A B).symm _)).2 x=_
    rw [Equiv.apply_symm_apply]
  simp_rw [hr,hc]

/- Exact product of all child path-event probabilities, for the real law. -/
theorem probability_split (z : ℝ) :
    H.probability z=(∏ y, (H.rowHoles y).probability z)*(∏ x, (H.columnHoles x).probability z) := by
  classical
  let (y : B.Slot) : Fintype {τ : A.Choices // (H.rowHoles y).Compatible τ} := Subtype.fintype _
  let (x : A.Slot) : Fintype {τ : B.Choices // (H.columnHoles x).Compatible τ} := Subtype.fintype _
  unfold probability
  rw [← H.splitCompatibleChoices.symm.sum_comp]
  simp_rw [H.splitCompatibleChoices_weight]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum]
  congr 1
  · exact (Fintype.prod_sum (fun y (τ : {τ : A.Choices // (H.rowHoles y).Compatible τ}) =>
      A.choiceWeight z τ.val)).symm
  · exact (Fintype.prod_sum (fun x (τ : {τ : B.Choices // (H.columnHoles x).Compatible τ}) =>
      B.choiceWeight z τ.val)).symm

/- Literal normalized conditional mass factors; no trajectory is reweighted. -/
theorem conditionalWeight_split (z : ℝ) (ω : {ω : (concat A B).Choices // H.Compatible ω}) :
    (concat A B).choiceWeight z ω.val/H.probability z=
      (∏ y, A.choiceWeight z (rowChoices A B ω.val y)/(H.rowHoles y).probability z)*
      (∏ x, B.choiceWeight z (columnChoices A B ω.val x)/(H.columnHoles x).probability z) := by
  rw [choiceWeight_split,H.probability_split]
  rw [Finset.prod_div_distrib,Finset.prod_div_distrib]
  exact mul_div_mul_comm _ _ _ _

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

/- Move the target's reference identification to the actual junction layer. -/

lemma sweep_refPair (hf : H.Feasible) :
    (concat A B).sweep (H.reference hf)=H.columnAction (H.refPair hf).2*H.rowAction (H.refPair hf).1 := by
  simpa only [refPair,Equiv.symm_apply_apply] using H.split_choice_sweep (H.refPair hf)

lemma junction_residual (hf : H.Feasible) (ω : {ω : (concat A B).Choices // H.Compatible ω}) :
    H.junctionEquiv hf (H.residual hf ω)=
      H.columnResidual hf (H.splitCompatibleChoices ω).2*H.rowResidual hf (H.splitCompatibleChoices ω).1 := by
  apply Subtype.ext
  change H.rowAction (H.refPair hf).1*(((concat A B).sweep (H.reference hf))⁻¹*
    (concat A B).sweep ω.val)*(H.rowAction (H.refPair hf).1)⁻¹=_
  have he : (concat A B).sweep ω.val=H.columnAction (H.splitCompatibleChoices ω).2*
      H.rowAction (H.splitCompatibleChoices ω).1 := by
    simpa only [Equiv.symm_apply_apply] using H.split_choice_sweep (H.splitCompatibleChoices ω)
  rw [H.sweep_refPair hf,he]
  change _=((H.columnAction (H.refPair hf).2)⁻¹*H.columnAction (H.splitCompatibleChoices ω).2)*
    (H.rowAction (H.splitCompatibleChoices ω).1*(H.rowAction (H.refPair hf).1)⁻¹)
  group

theorem junction_average_split {n : Type*} [Fintype n] [DecidableEq n]
    (hf : H.Feasible) (z : ℝ) (τ : H.JunctionFix →* Matrix n n ℂ) :
    (∑ ω : {ω : (concat A B).Choices // H.Compatible ω},
      (((concat A B).choiceWeight z ω.val/H.probability z : ℝ) : ℂ) •
        τ (H.junctionEquiv hf (H.residual hf ω)))=
      H.columnAverage hf z τ*H.rowAverage hf z τ := by
  classical
  let (y : B.Slot) : Fintype {ω : A.Choices // (H.rowHoles y).Compatible ω} := Subtype.fintype _
  let (x : A.Slot) : Fintype {ω : B.Choices // (H.columnHoles x).Compatible ω} := Subtype.fintype _
  rw [← H.splitCompatibleChoices.symm.sum_comp]
  simp_rw [H.junction_residual,Equiv.apply_symm_apply,map_mul,H.conditionalWeight_split,
    Complex.ofReal_mul]
  unfold columnAverage rowAverage
  rw [Matrix.sum_mul]
  simp_rw [Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro r _
  have he := H.splitCompatibleChoices.apply_symm_apply (r,c)
  have hr : rowChoices A B (H.splitCompatibleChoices.symm (r,c)).val=fun y => (r y).val := by
    change ((choicesSplit A B) ((choicesSplit A B).symm _)).1=_
    rw [Equiv.apply_symm_apply]
  have hc : columnChoices A B (H.splitCompatibleChoices.symm (r,c)).val=fun x => (c x).val := by
    change ((choicesSplit A B) ((choicesSplit A B).symm _)).2=_
    rw [Equiv.apply_symm_apply]
  simp only [hr,hc]
  rw [mul_comm]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps

namespace Grid.Holes

variable {G : Grid} {h : ℕ}

/- Average of the remaining random bijection, conditioned on the entire paths,
not only endpoints. The reference affects only unitary identifications. -/

theorem probability_pos (H : G.Holes h) (hf : H.Feasible) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1) : 0 < H.probability z := by
  let : Nonempty {ω : G.Choices // H.Compatible ω} :=
    ⟨⟨H.reference hf, H.reference_compatible hf⟩⟩
  apply Finset.sum_pos
  · intro ω _
    exact G.choiceWeight_pos hz hz' ω.val
  · exact Finset.univ_nonempty

theorem conditionalAverage_eq_sum (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ρ =
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        ((G.choiceWeight z ω.val / H.probability z : ℝ) : ℂ) •
          ρ.matrix (H.residual hf ω) := by
  simp only [conditionalAverage, Finset.smul_sum, smul_smul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_comm]

theorem conditionalAverage_norm_le (H : G.Holes h) (hf : H.Feasible) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1) (ρ : UnitaryIrrep H.stabilizer) :
    ‖H.conditionalAverage hf z ρ‖ ≤ 1 := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  rw [H.conditionalAverage_eq_sum hf z ρ]
  apply unitary_average_norm_le
  · intro ω
    exact div_nonneg (G.choiceWeight_pos hz hz' ω.val).le (H.probability_pos hf hz hz').le
  · rw [← Finset.sum_div]
    exact div_self (H.probability_pos hf hz hz').ne'
  · intro ω
    exact ρ.unitary (H.residual hf ω)

theorem conditionalMoment_nonneg (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) (q : ℕ) :
    0 ≤ schattenMoment q (H.conditionalAverage hf z ρ) :=
  trace_moment_nonneg _ _

theorem conditionalMoment_le_dimension (H : G.Holes h) (hf : H.Feasible) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1) (ρ : UnitaryIrrep H.stabilizer) (q : ℕ) :
    schattenMoment q (H.conditionalAverage hf z ρ) ≤ ρ.dimension := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  apply (trace_moment_le _ q).trans
  have hn := H.conditionalAverage_norm_le hf hz hz' ρ
  have hp : ‖H.conditionalAverage hf z ρ‖^(2*q) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hn
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hp

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
-- module Solutions.OAIQ56_CS.SignedTensor_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

namespace SignedTensor

/- p even basis symbols followed by p odd ones, exactly E⊕O in05. -/
theorem matrix_unitary {p l : ℕ} (σ : Equiv.Perm (Fin l)) :
    (matrix (p := p) σ).conjTranspose * matrix σ=1 := by
  ext u w
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,matrix]
  rw [Finset.sum_eq_single (wordPerm σ u)]
  · by_cases hu : u=w
    · subst w
      simp only [ite_true,Matrix.one_apply_eq,phase_star_mul]
    · have hne : wordPerm σ u ≠ wordPerm σ w :=
        fun hh => hu ((wordPerm σ).injective hh)
      simp [hne,hu]
  · intro v hv hne
    simp [hne]
  · simp

lemma densityPower_mul {p : ℕ} (l : ℕ) (a b : Matrix (Letter p) (Letter p) ℂ) :
    densityPower l (a*b)=densityPower l a * densityPower l b := by
  ext u w
  simp only [densityPower,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

lemma densityPower_star {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ) :
    densityPower l r.conjTranspose=(densityPower l r).conjTranspose := by
  ext u w
  simp [densityPower,Matrix.conjTranspose_apply]

lemma densityPower_trace {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ) :
    Matrix.trace (densityPower l r)=(Matrix.trace r)^l := by
  change (∑ w : Word p l, ∏ i, r (w i) (w i))=(∑ i, r i i)^l
  exact (Fintype.sum_pow (fun i : Letter p => r i i) l).symm

open scoped MatrixOrder in
lemma densityPower_posSemidef {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : r.PosSemidef) : (densityPower l r).PosSemidef := by
  obtain ⟨b,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hr.nonneg
  rw [densityPower_mul,Matrix.star_eq_conjTranspose,densityPower_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/- Even means positive trace-one and block diagonal for E,O, exactly as in05. -/

lemma phase_eq_of_parity {p l : ℕ} (σ : Equiv.Perm (Fin l))
    (u w : Word p l) (h : ∀ i, odd (u i) ↔ odd (w i)) : phase σ u=phase σ w := by
  simp only [phase,koszulExponent]
  congr 2
  apply Finset.filter_congr
  intro ij hij
  rw [h ij.1,h ij.2]

lemma densityPower_permute {p l : ℕ} (σ : Equiv.Perm (Fin l))
    (r : Matrix (Letter p) (Letter p) ℂ) (u w : Word p l) :
    densityPower l r (wordPerm σ u) (wordPerm σ w)=densityPower l r u w := by
  simp only [densityPower,wordPerm,Equiv.coe_fn_mk]
  exact Equiv.prod_comp σ⁻¹ (fun i => r (u i) (w i))

/- Even densities commute with the signed action; omission of evenness here
would be false. This is also the block-reordering claim at the end of05. -/

end SignedTensor
end CoordinateSweeps

/- A direct counting approach to the polynomial multiplicity bound in05,
without replacing Schur-Weyl or the density inequality by an axiom.
The signed tensor commutant is determined by pair-word histograms. -/
namespace CoordinateSweeps.SignedTensor

lemma profile_fiber_card {p l : ℕ} (u w : Word p l) (a : Letter p × Letter p) :
    Fintype.card {i : Fin l // (u i,w i)=a}=(profile u w a).val := by
  simp [profile,Fintype.card_subtype]

/- Two word pairs have the same histogram exactly when a position permutation
carries one to the other. This supplies the finite orbit-counting parameter. -/
lemma profile_eq_exists_perm {p l : ℕ} {u w u' w' : Word p l}
    (hh : profile u w=profile u' w') :
    ∃ σ : Equiv.Perm (Fin l), wordPerm σ u=u' ∧ wordPerm σ w=w' := by
  have hc (a : Letter p × Letter p) : Fintype.card {i : Fin l // (u i,w i)=a}=
      Fintype.card {i : Fin l // (u' i,w' i)=a} := by
    rw [profile_fiber_card,profile_fiber_card,hh]
  let e (a : Letter p × Letter p) : {i : Fin l // (u i,w i)=a} ≃
      {i : Fin l // (u' i,w' i)=a} := Fintype.equivOfCardEq (hc a)
  let σ : Equiv.Perm (Fin l) := Equiv.ofFiberEquiv e
  have he (i : Fin l) : (u' (σ i),w' (σ i))=(u i,w i) := Equiv.ofFiberEquiv_map e i
  refine ⟨σ,?_,?_⟩
  · funext i
    have hi := congrArg Prod.fst (he (σ⁻¹ i))
    simpa [wordPerm] using hi.symm
  · funext i
    have hi := congrArg Prod.snd (he (σ⁻¹ i))
    simpa [wordPerm] using hi.symm

lemma profileRep_spec {p l : ℕ} (q : OccurringProfile p l) :
    profile (profileRep q).1 (profileRep q).2=q.val := Classical.choose_spec q.property

lemma commutantEval_injective (p l : ℕ) : Function.Injective (commutantEval p l) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro A hA
  apply Subtype.ext
  ext u w
  let q : OccurringProfile p l := ⟨profile u w,Set.mem_range_self (u,w)⟩
  have he : A.val (profileRep q).1 (profileRep q).2=0 := congrFun hA q
  have hp : profile (profileRep q).1 (profileRep q).2=profile u w := profileRep_spec q
  obtain ⟨σ,hσu,hσw⟩ := profile_eq_exists_perm hp
  have hh := commutant_zero_transport A σ he
  simpa [hσu,hσw] using hh

/- Polynomial signed-commutant bound of exactly the O(p² log(s+1)) scale
required by the main induction. No classification of partitions is used. -/
theorem commutant_finrank_le (p l : ℕ) :
    Module.finrank ℂ (commutant p l) ≤ (l+1)^((2*p)*(2*p)) := by
  have h := LinearMap.finrank_le_finrank_of_injective (commutantEval_injective p l)
  have hc : Fintype.card (OccurringProfile p l) ≤ Fintype.card (Profile p l) :=
    Fintype.card_subtype_le _
  have he : Fintype.card (Profile p l)=(l+1)^((2*p)*(2*p)) := by
    simp [Profile,Letter]
  simpa [he] using h.trans (by simpa using hc)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor

lemma matrix_inv {p l : ℕ} (σ : Equiv.Perm (Fin l)) :
    matrix (p := p) σ⁻¹=(matrix (p := p) σ).conjTranspose := by
  calc
    matrix σ⁻¹=1*matrix (p := p) σ⁻¹ := (one_mul _).symm
    _ = ((matrix σ).conjTranspose*matrix σ)*matrix (p := p) σ⁻¹ := by rw [matrix_unitary]
    _ = (matrix (p := p) σ).conjTranspose := by
      rw [mul_assoc,← matrix_mul,mul_inv_cancel,matrix_one,mul_one]

lemma endomorphismMatrix_injective (p l : ℕ) :
    Function.Injective (endomorphismMatrix p l) := by
  intro F H hh
  apply Representation.IntertwiningMap.ext
  exact LinearMap.toMatrixAlgEquiv'.injective (congrArg Subtype.val hh)

theorem tensor_endomorphisms_finrank_le (p l : ℕ) :
    Module.finrank ℂ ((tensorRepresentation p l).IntertwiningMap (tensorRepresentation p l)) ≤
      (l+1)^((2*p)*(2*p)) :=
  (LinearMap.finrank_le_finrank_of_injective (endomorphismMatrix_injective p l)).trans
    (commutant_finrank_le p l)

/- The polynomial multiplicity clause of05 signed density lemma, proved
without Young diagrams. Multiplicity is the actual space of equivariant embeddings. -/
theorem multiplicity_le (p l : ℕ) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)) ≤
      (l+1)^((2*p)*(2*p)) := by
  have hh := ρ.multiplicity_sq_le_commutant (action p l)
    (fun σ => matrix_inv σ |>.symm)
  have hm : Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)) ≤
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)))^2 := by
    exact Nat.le_self_pow (by omega) _
  exact hm.trans (hh.trans (tensor_endomorphisms_finrank_le p l))

lemma isotypic_eq_projector {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    isotypic (p := p) ρ=ρ.projector (action p l) := by
  simp only [isotypic,UnitaryIrrep.projector,UnitaryIrrep.coefficient,Finset.smul_sum,mul_smul]
  rfl

theorem isotypic_posSemidef {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    (isotypic (p := p) ρ).PosSemidef := by
  rw [isotypic_eq_projector]
  exact ρ.projector_posSemidef (action p l) (fun σ => (matrix_inv σ).symm)

theorem isotypic_trace {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Matrix.trace (isotypic (p := p) ρ)=(ρ.dimension : ℂ)*
      Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)) := by
  rw [isotypic_eq_projector]
  simp only [UnitaryIrrep.projector,Matrix.trace_sum,Matrix.trace_smul,
    UnitaryIrrep.coefficient,smul_eq_mul]
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card (Equiv.Perm (Fin l)) : ℂ)) *
        ∑ σ, Matrix.trace (action p l σ)*Matrix.trace (ρ.matrix σ⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = _ := by
      rw [ρ.character_sum_multiplicity (action p l)]
      have hN : (Fintype.card (Equiv.Perm (Fin l)) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

end CoordinateSweeps.SignedTensor

/- Mismatched symbols in a purification
obey a Pauli exclusion rule. This is derived from the literal Koszul action. -/

namespace CoordinateSweeps.SignedTensor
/- The actual Koszul regrouping phase from (V⊗V̄)^⊗l to
V^⊗l⊗V̄^⊗l. It will cancel, not be dropped, under partial trace. -/

lemma phase_square {p l : ℕ} (σ : Equiv.Perm (Fin l)) (u : Word p l) :
    phase σ u * phase σ u = 1 := by
  simpa only [phase,star_pow,star_neg,star_one] using phase_star_mul σ u

lemma regroupPhase_square {p l : ℕ} (u w : Word p l) :
    regroupPhase u w * regroupPhase u w = 1 := by
  unfold regroupPhase
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro ij _
  split_ifs <;> norm_num

lemma regroupPhase_star {p l : ℕ} (u w : Word p l) :
    star (regroupPhase u w) = regroupPhase u w := by
  unfold regroupPhase
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro ij _
  split_ifs <;> simp

/- Permutations of the matched slots have no residual super-sign after
literal Koszul regrouping; the positions of mismatched symbols are fixed. -/
theorem regroupPhase_permute {p l : ℕ} (σ : Equiv.Perm (Fin l)) (u w : Word p l)
    (hfix : ∀ i, (odd (u i) ↔ ¬ odd (w i)) → σ i = i) :
    regroupPhase (wordPerm σ u) (wordPerm σ w) * phase σ u * phase σ w =
      regroupPhase u w := by
  unfold regroupPhase
  rw [phase_prod,phase_prod]
  have hreindex :
      (∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm σ u ij.1) ∧ odd (wordPerm σ w ij.2) then (-1 : ℂ) else 1)) =
      ∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm σ u (Equiv.Perm.signBijAux σ ij).1) ∧
          odd (wordPerm σ w (Equiv.Perm.signBijAux σ ij).2) then (-1 : ℂ) else 1) := by
    symm
    exact Finset.prod_nbij (Equiv.Perm.signBijAux σ)
      Equiv.Perm.signBijAux_mem Equiv.Perm.signBijAux_injOn
      Equiv.Perm.signBijAux_surj (fun _ _ => rfl)
  rw [hreindex,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  rintro ⟨i,j⟩ hij
  have hji : j < i := Equiv.Perm.mem_finPairsLT.mp hij
  have hne : σ j ≠ σ i := σ.injective.ne hji.ne
  by_cases ht : σ j < σ i
  · simp [Equiv.Perm.signBijAux,wordPerm,ht,ht.not_gt]
  · have ht' : σ i < σ j := lt_of_le_of_ne (le_of_not_gt ht) hne.symm
    have hm : ¬ ((odd (u i) ↔ ¬ odd (w i)) ∧ (odd (u j) ↔ ¬ odd (w j))) := by
      rintro ⟨hi,hj⟩
      have hi' := hfix i hi
      have hj' := hfix j hj
      rw [hi',hj'] at ht'
      exact hji.not_gt ht'
    by_cases hui : odd (u i) <;> by_cases huj : odd (u j) <;>
      by_cases hwi : odd (w i) <;> by_cases hwj : odd (w j) <;>
      simp [Equiv.Perm.signBijAux,wordPerm,ht,ht',hui,huj,hwi,hwj] at hm ⊢

lemma commutant_transport {p l : ℕ} (A : commutant p l) (σ : Equiv.Perm (Fin l))
    (u w : Word p l) :
    A.val (wordPerm σ u) (wordPerm σ w) = phase σ u * phase σ w * A.val u w := by
  have hh := congrArg (fun B : Matrix (Word p l) (Word p l) ℂ => B (wordPerm σ u) w)
    (A.property σ)
  rw [mul_signed_entry,signed_mul_entry] at hh
  calc
    _ = (A.val (wordPerm σ u) (wordPerm σ w) * phase σ w) * phase σ w := by
      rw [mul_assoc,phase_square,mul_one]
    _ = (phase σ u * A.val u w) * phase σ w := by rw [hh]
    _ = _ := by ring

/- Rephased purification components are ordinary symmetric on the free,
matched-pair slots, a proved conclusion from the signed commutant relation. -/
theorem regrouped_commutant_invariant {p l : ℕ} (A : commutant p l)
    (σ : Equiv.Perm (Fin l)) (u w : Word p l)
    (hfix : ∀ i, (odd (u i) ↔ ¬ odd (w i)) → σ i = i) :
    regroupPhase (wordPerm σ u) (wordPerm σ w) *
        A.val (wordPerm σ u) (wordPerm σ w) = regroupPhase u w * A.val u w := by
  rw [commutant_transport]
  calc
    _ = (regroupPhase (wordPerm σ u) (wordPerm σ w) * phase σ u * phase σ w) * A.val u w := by ring
    _ = _ := by rw [regroupPhase_permute σ u w hfix]

/- Equal local parities in the system copies give equal regrouping signs.
This is what justifies cancellation under the actual auxiliary partial trace. -/
lemma regroupPhase_of_same_parity {p l : ℕ} (u u' w : Word p l)
    (h : ∀ i, odd (u i) ↔ odd (u' i)) : regroupPhase u w = regroupPhase u' w := by
  unfold regroupPhase
  apply Finset.prod_congr rfl
  intro ij _
  rw [h ij.1]
end CoordinateSweeps.SignedTensor

end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Tensor_Postselection
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

namespace CoordinateSweeps.OrdinaryTensor
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

/- Occupancies of single alphabet symbols in an ordinary tensor word. -/

omit [Fintype A] [DecidableEq I] in
lemma count_le (w : I → A) (a : A) : count w a ≤ Fintype.card I := Fintype.card_subtype_le _

omit [Fintype A] [DecidableEq I] in
lemma counts_eq_exists_perm {u w : I → A} (h : count u = count w) :
    ∃ σ : Equiv.Perm I, permute σ u = w := by
  let e (a : A) : {i : I // u i = a} ≃ {i : I // w i = a} :=
    Fintype.equivOfCardEq (congrFun h a)
  let σ : Equiv.Perm I := Equiv.ofFiberEquiv e
  refine ⟨σ, ?_⟩
  ext i
  have hi : w (σ (σ⁻¹ i)) = u (σ⁻¹ i) := Equiv.ofFiberEquiv_map e (σ⁻¹ i)
  change u (σ⁻¹ i) = w i
  simpa using hi.symm

/- Word-preserving permutations and independent permutations of its fibers
are literally equivalent finite sets. This yields the factorial frame moments. -/

lemma card_wordStabilizer (w : I → A) :
    Fintype.card {σ : Equiv.Perm I // ∀ i, w (σ i) = w i} =
      ∏ a : A, (count w a).factorial := by
  rw [Fintype.card_congr (fiberPermEquiv w), Fintype.card_pi]
  simp only [Fintype.card_perm, count]

/- A transporter fiber is a coset of the literal word stabilizer. -/

lemma card_transporter (u w : I → A) :
    Fintype.card {g : Equiv.Perm I // permute g u = w} =
      if count u = count w then ∏ a, (count u a).factorial else 0 := by
  split_ifs with h
  · obtain ⟨σ,hσ⟩ := counts_eq_exists_perm h
    rw [Fintype.card_congr (transporterEquiv u w σ hσ), card_wordStabilizer]
  · have : IsEmpty {g : Equiv.Perm I // permute g u = w} :=
      ⟨fun g => h (by rw [← g.property, permute_count])⟩
    exact Fintype.card_eq_zero

/- The finite moment matrix which will be realized by actual radial Gamma
variables and root phases rather than an assumed de Finetti density. -/
end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor

/- A factorial ratio is bounded by the largest factor; used to avoid
any assumed entropy/Stirling estimate in the empirical postselection measure. -/
lemma factorial_step_upper (t k : ℕ) : (t+k).factorial ≤ t.factorial * (t+k)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (t+(k+1)).factorial = (t+k+1)*(t+k).factorial := by rw [← Nat.add_assoc, Nat.factorial_succ]
      _ ≤ (t+k+1)*(t.factorial*(t+k)^k) := Nat.mul_le_mul_left _ ih
      _ ≤ (t+k+1)*(t.factorial*(t+k+1)^k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      _ = t.factorial*(t+(k+1))^(k+1) := by rw [pow_succ]; ring

/- For any integral Poisson mean n, n is a mode. This elementary exact
inequality is the only numerical ingredient for the finite tensor mixture. -/
lemma factorial_mode (n t : ℕ) : n^t * n.factorial ≤ n^n * t.factorial := by
  rcases le_total t n with h | h
  · have hu : n.factorial ≤ t.factorial*n^(n-t) := by
      simpa only [Nat.add_sub_of_le h] using factorial_step_upper t (n-t)
    calc
      _ ≤ n^t * (t.factorial*n^(n-t)) := Nat.mul_le_mul_left _ hu
      _ = n^n*t.factorial := by rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le h]; ring
  · have hl := Nat.factorial_mul_pow_sub_le_factorial h
    calc
      n^t*n.factorial = n^n*(n.factorial*n^(t-n)) := by
        rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le h]; ring
      _ ≤ n^n*t.factorial := Nat.mul_le_mul_left _ hl

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

omit [DecidableEq I] in
lemma prod_word_eq_counts {R : Type*} [CommMonoid R] (r : A → R) (w : I → A) :
    (∏ i, r (w i)) = ∏ a, r a ^ count w a := by
  rw [← Finset.prod_fiberwise' Finset.univ w r]
  simp only [Finset.prod_const, ← Fintype.card_subtype, count]

/- Exact sigma decomposition of a word orbit and its transporter fibers. -/

lemma orbit_card_mul_factorials (u : I → A) :
    Fintype.card {w : I → A // count w = count u} * (∏ a, (count u a).factorial) =
      (Fintype.card I).factorial := by
  have he := Fintype.card_congr (orbitFiberEquiv u)
  rw [Fintype.card_sigma, Fintype.card_perm] at he
  calc
    _ = ∑ _w : {w : I → A // count w = count u}, (∏ a, (count u a).factorial) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = ∑ w : {w : I → A // count w = count u},
        Fintype.card {σ : Equiv.Perm I // permute σ u = w.val} := by
      apply Finset.sum_congr rfl
      intro w _
      rw [card_transporter, ite_eq_left w.property.symm]
    _ = _ := he

/- Histogram space is an actual finite set of attained occupancies. -/

omit [DecidableEq I] in
lemma histogram_surjective : Function.Surjective (histogram (I := I) (A := A)) := by
  rintro ⟨h,⟨w,hw⟩⟩
  exact ⟨w,Subtype.ext hw⟩

omit [DecidableEq I] in
lemma histogram_card_le : Fintype.card (Histogram I A) ≤ (Fintype.card I+1)^Fintype.card A := by
  let f : Histogram I A → (A → Fin (Fintype.card I+1)) := fun h a =>
    ⟨h.val a, by obtain ⟨w,hw⟩ := h.property; rw [← hw]; exact Nat.lt_succ_of_le (count_le w a)⟩
  have hf : Function.Injective f := by
    intro h k he
    apply Subtype.ext
    funext a
    exact congrArg Fin.val (congrFun he a)
  simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf

/- The individual multinomial type of a word, evaluated at any integer weights. -/

lemma typeWeight_mul_factorials (r : A → ℕ) (u : I → A) :
    typeWeight r u * (∏ a, (count u a).factorial) =
      (Fintype.card I).factorial * (∏ a, r a ^ count u a) := by
  rw [typeWeight, mul_right_comm, orbit_card_mul_factorials]

/- Empirical occupancies maximize their own exact multinomial type weight. -/
lemma typeWeight_empirical_max (u w : I → A) : typeWeight (count u) w ≤ typeWeight (count u) u := by
  have hu : 0 < ∏ a : A, (count u a).factorial :=
    Finset.prod_pos (fun a _ => Nat.factorial_pos _)
  have hw : 0 < ∏ a : A, (count w a).factorial :=
    Finset.prod_pos (fun a _ => Nat.factorial_pos _)
  apply Nat.le_of_mul_le_mul_right (c := ∏ a, (count w a).factorial) _ hw
  apply Nat.le_of_mul_le_mul_right (c := ∏ a, (count u a).factorial) _ hu
  calc
    _ = (Fintype.card I).factorial *
        ((∏ a, count u a ^ count w a) * (∏ a, (count u a).factorial)) := by
      rw [typeWeight_mul_factorials, mul_assoc]
    _ ≤ (Fintype.card I).factorial *
        ((∏ a, count u a ^ count u a) * (∏ a, (count w a).factorial)) := by
      apply Nat.mul_le_mul_left
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod' (fun a _ => factorial_mode (count u a) (count w a))
    _ = _ := by rw [mul_right_comm (typeWeight _ _), typeWeight_mul_factorials, mul_assoc]

/- Type weight on the finite, attained histogram space. -/

lemma histogramWeight_mk (r : A → ℕ) (u : I → A) :
    histogramWeight r (histogram u) = typeWeight r u := by
  unfold histogramWeight typeWeight
  congr 1
  apply Fintype.card_congr
  exact { toFun := fun w => ⟨w.val, congrArg Subtype.val w.property⟩
          invFun := fun w => ⟨w.val, Subtype.ext w.property⟩
          left_inv := fun w => Subtype.ext rfl
          right_inv := fun w => Subtype.ext rfl }

lemma sum_histogramWeight (r : A → ℕ) :
    (∑ h : Histogram I A, histogramWeight r h) = (∑ a, r a)^Fintype.card I := by
  have ht := Finset.sum_prod_piFinset (Finset.univ : Finset A) (fun _i : I => r)
  simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ] at ht
  rw [← ht, ← Fintype.sum_fiberwise (histogram (I := I) (A := A))]
  apply Finset.sum_congr rfl
  intro h _
  change Fintype.card {w : I → A // histogram w = h} * (∏ a, r a^h.val a) =
    ∑ w : {w : I → A // histogram w = h}, ∏ i, r (w.val i)
  have he (w : {w : I → A // histogram w = h}) :
      (∏ i, r (w.val i)) = ∏ a, r a ^ h.val a := by
    rw [prod_word_eq_counts, show count w.val = h.val from congrArg Subtype.val w.property]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

/- Exact polynomial empirical multinomial lower bound. It includes zero
occupancies and avoids Stirling errors and asymptotic hypotheses. -/
theorem empirical_type_mass (u : I → A) :
    (Fintype.card I)^Fintype.card I ≤
      (Fintype.card I+1)^Fintype.card A * typeWeight (count u) u := by
  have he := sum_histogramWeight (I := I) (count u)
  rw [sum_count] at he
  calc
    _ = ∑ h : Histogram I A, histogramWeight (count u) h := he.symm
    _ ≤ ∑ _h : Histogram I A, typeWeight (count u) u := by
      apply Finset.sum_le_sum
      intro h _
      obtain ⟨w,rfl⟩ := histogram_surjective h
      rw [histogramWeight_mk]
      exact typeWeight_empirical_max u w
    _ = Fintype.card (Histogram I A) * typeWeight (count u) u := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right _ (histogram_card_le (I := I) (A := A))
end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open AddChar
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

/- Finite independent root phases. The modulus is strictly larger than
any occupancy, so it distinguishes every histogram without an analytic limit. -/

omit [DecidableEq I] in
lemma wordPhase_eq_prod (t : PhaseSpace I A) (w : I → A) :
    wordPhase t w = ∏ i, ZMod.stdAddChar (t (w i)) := by
  rw [prod_word_eq_counts (fun a : A => ZMod.stdAddChar (t a)) w]
  unfold wordPhase
  apply Finset.prod_congr rfl
  intro a _
  simpa only [nsmul_eq_mul, mul_comm] using
    (map_nsmul_eq_pow (ZMod.stdAddChar (N := Fintype.card I+1)) (count w a) (t a))

omit [DecidableEq I] in
lemma phase_conjugate_sum (c d : A → ℕ) (hc : ∀ a, c a ≤ Fintype.card I)
    (hd : ∀ a, d a ≤ Fintype.card I) :
    (∑ t : PhaseSpace I A,
      (∏ a, ZMod.stdAddChar (t a * (c a : ZMod (Fintype.card I+1)))) *
        star (∏ a, ZMod.stdAddChar (t a * (d a : ZMod (Fintype.card I+1))))) =
      if c = d then (Fintype.card (PhaseSpace I A) : ℂ) else 0 := by
  simp only [star_prod]
  simp_rw [← Finset.prod_mul_distrib, Complex.star_def, ← AddChar.map_neg_eq_conj,
    ← map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
  have hf := Finset.sum_prod_piFinset (Finset.univ : Finset (ZMod (Fintype.card I+1)))
    (fun a x => ZMod.stdAddChar (x * ((c a : ZMod (Fintype.card I+1)) - (d a : ZMod (Fintype.card I+1)))))
  simp only [Fintype.piFinset_univ] at hf
  rw [hf]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _)]
  have he (a : A) : (c a : ZMod (Fintype.card I+1)) - (d a : ZMod (Fintype.card I+1)) = 0 ↔ c a = d a := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hc a)), Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hd a))]
  simp_rw [he]
  by_cases h : c = d
  · simp [h, ZMod.card]
  · rw [ite_eq_right h]
    obtain ⟨a,ha⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

/- Exact finite orthogonality of different empirical type phases. -/
omit [DecidableEq I] in
lemma wordPhase_orthogonality (u w : I → A) :
    (∑ t : PhaseSpace I A, wordPhase t u * star (wordPhase t w)) =
      if count u = count w then (Fintype.card (PhaseSpace I A) : ℂ) else 0 :=
  phase_conjugate_sum (count u) (count w) (count_le u) (count_le w)

/- Every root-phase component has unit modulus. -/
end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open AddChar
open scoped ComplexOrder
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

lemma outer_posSemidef {J : Type*} [Finite J] (v : J → ℂ) : (outer v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

lemma outer_apply {J : Type*} (v : J → ℂ) (i j : J) : outer v i j = v i * star (v j) := rfl

/- Empirical-site amplitudes. Their exact squared norm is one when there is
at least one slot. Zero-count letters are allowed and have zero amplitude. -/

omit [DecidableEq I] in
lemma amplitude_eq_counts (h : Histogram I A) (w : I → A) :
    amplitude h w = ∏ a, (Real.sqrt ((h.val a : ℝ)/Fintype.card I)) ^ count w a :=
by
  unfold amplitude
  exact prod_word_eq_counts (fun a => Real.sqrt ((h.val a : ℝ)/Fintype.card I)) w

omit [DecidableEq I] in
lemma amplitude_congr (h : Histogram I A) {u w : I → A} (he : count u = count w) :
    amplitude h u = amplitude h w := by rw [amplitude_eq_counts, amplitude_eq_counts, he]

omit [DecidableEq I] in
lemma tensorVector_empirical (h : Histogram I A) (t : PhaseSpace I A) (w : I → A) :
    tensorVector (empiricalVector h t) w = (amplitude h w : ℂ) * wordPhase t w := by
  rw [wordPhase_eq_prod]
  simp only [tensorVector, empiricalVector, amplitude, Complex.ofReal_prod, Finset.prod_mul_distrib]

omit [DecidableEq I] in
lemma amplitude_square (h : Histogram I A) (w : I → A) :
    amplitude h w ^ 2 = (∏ a, (h.val a : ℝ) ^ count w a) /
      (Fintype.card I : ℝ) ^ Fintype.card I := by
  rw [amplitude_eq_counts, ← Finset.prod_pow]
  simp_rw [← pow_mul, mul_comm _ 2, pow_mul, Real.sq_sqrt (by positivity :
    0 ≤ (h.val _ : ℝ)/Fintype.card I), div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_count]

/- Finite phase average of actual pure product states. -/

omit [DecidableEq I] in
lemma phaseSpace_card_pos : 0 < Fintype.card (PhaseSpace I A) := by
  rw [Fintype.card_fun, ZMod.card]
  positivity

omit [DecidableEq I] in
lemma phaseFrame_posSemidef (h : Histogram I A) : (phaseFrame h).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum _ (fun t _ => outer_posSemidef _)
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

omit [DecidableEq I] in
lemma phaseFrame_entry (h : Histogram I A) (u w : I → A) :
    phaseFrame h u w = if count u = count w then ((amplitude h u : ℂ)^2) else 0 := by
  simp only [phaseFrame, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, outer_apply,
    tensorVector_empirical, star_mul, RCLike.star_def, Complex.conj_ofReal]
  have he (t : PhaseSpace I A) :
      ((amplitude h u : ℂ)*wordPhase t u) *
        (star (wordPhase t w)*(amplitude h w : ℂ)) =
      ((amplitude h u : ℂ)*(amplitude h w : ℂ)) * (wordPhase t u * star (wordPhase t w)) := by ring
  simp only [← Complex.star_def]
  simp_rw [he]
  rw [← Finset.mul_sum, wordPhase_orthogonality]
  split_ifs with hc
  · rw [amplitude_congr h hc]
    have hn : (Fintype.card (PhaseSpace I A) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt phaseSpace_card_pos)
    field_simp
  · simp
end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open scoped ComplexOrder
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

omit [DecidableEq I] in
lemma count_representative (h : Histogram I A) : count (representative h) = h.val :=
  Classical.choose_spec h.property
omit [DecidableEq I] in
lemma histogram_representative (h : Histogram I A) : histogram (representative h) = h :=
  Subtype.ext (count_representative h)

lemma orbitSize_pos (h : Histogram I A) : 0 < orbitSize h := by
  have : Nonempty {w : I → A // histogram w = h} := ⟨⟨representative h, histogram_representative h⟩⟩
  exact Fintype.card_pos

lemma orbitSize_mk (w : I → A) :
    orbitSize (histogram w) = Fintype.card {u : I → A // count u = count w} := by
  have he := histogramWeight_mk (fun _ : A => 1) w
  simpa only [histogramWeight,typeWeight,one_pow,Finset.prod_const_one,mul_one,orbitSize] using he

omit [DecidableEq I] in
lemma block_posSemidef (h : Histogram I A) : (block h).PosSemidef := outer_posSemidef _

omit [DecidableEq I] in
lemma block_entry (h : Histogram I A) (u w : I → A) :
    block h u w = if histogram u = h ∧ histogram w = h then (1 : ℂ) else 0 := by
  simp only [block,outer_apply]
  split_ifs <;> simp_all

/- Orthogonal projection onto vectors invariant under ordinary slot
permutations, implemented by their exact histogram blocks. -/

lemma symProjector_posSemidef : (symProjector (I := I) (A := A)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro h _
  exact (block_posSemidef h).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma symProjector_entry (u w : I → A) : symProjector u w =
    if histogram u = histogram w then (orbitSize (histogram u) : ℂ)⁻¹ else 0 := by
  simp only [symProjector, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, block_entry]
  rw [Finset.sum_eq_single (histogram u)]
  · by_cases h : histogram u = histogram w <;> simp [h,eq_comm]
  · intro h _ hne
    have he : histogram u ≠ h := Ne.symm hne
    simp [he]
  · simp

lemma symProjector_mulVec_of_constant (v : (I → A) → ℂ)
    (hv : ∀ u w, count u = count w → v u = v w) :
    (symProjector (I := I) (A := A)).mulVec v = v := by
  ext u
  simp only [Matrix.mulVec, dotProduct, symProjector_entry, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have he (w : I → A) (hw : w ∈ Finset.univ.filter (fun w => histogram u = histogram w)) : v w = v u :=
    (hv u w (congrArg Subtype.val (Finset.mem_filter.mp hw).2)).symm
  rw [Finset.sum_congr rfl (fun w hw => congrArg ((orbitSize (histogram u) : ℂ)⁻¹ * ·) (he w hw))]
  simp only [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
  have hc : Fintype.card {w : I → A // histogram u = histogram w} = orbitSize (histogram u) := by
    unfold orbitSize
    apply Fintype.card_congr
    exact { toFun := fun w => ⟨w.val,w.property.symm⟩
            invFun := fun w => ⟨w.val,w.property.symm⟩
            left_inv := fun w => Subtype.ext rfl
            right_inv := fun w => Subtype.ext rfl }
  rw [hc]
  have ho : (orbitSize (histogram u) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (orbitSize_pos _))
  field_simp

lemma symProjector_idempotent : (symProjector (I := I) (A := A)) * symProjector = symProjector := by
  ext u w
  have he := symProjector_mulVec_of_constant (fun v : I → A => symProjector v w) (fun v v' h => by
    have hh : histogram v = histogram v' := Subtype.ext h
    simp only [symProjector_entry, hh])
  exact congrFun he u

omit [DecidableEq I] in
lemma histogramAmplitude_mk (h : Histogram I A) (w : I → A) :
    histogramAmplitude h (histogram w) = amplitude h w := by
  apply amplitude_congr
  exact count_representative _

omit [DecidableEq I] in
lemma phaseFrame_blocks (h : Histogram I A) :
    phaseFrame h = ∑ k : Histogram I A, ((histogramAmplitude h k : ℂ)^2) • block k := by
  ext u w
  rw [phaseFrame_entry]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, block_entry]
  rw [Finset.sum_eq_single (histogram u)]
  · have he : (count u = count w) ↔ histogram w = histogram u :=
      ⟨fun h => Subtype.ext h.symm, fun h => (congrArg Subtype.val h).symm⟩
    rw [histogramAmplitude_mk]
    simp only [true_and, he]
    split_ifs <;> simp
  · intro k _ hk
    have he : histogram u ≠ k := Ne.symm hk
    simp [he]
  · simp

/- Polynomial inverse-orbit bound for the **actual** empirical phase frame. -/
lemma inverse_orbit_le_empirical (hn : 0 < Fintype.card I) (h : Histogram I A) :
    (orbitSize h : ℝ)⁻¹ ≤ ((Fintype.card I+1)^Fintype.card A : ℕ) * histogramAmplitude h h ^ 2 := by
  obtain ⟨u,rfl⟩ := histogram_surjective h
  rw [histogramAmplitude_mk, orbitSize_mk, amplitude_square]
  have ho : (0 : ℝ) < Fintype.card {w : I → A // count w = count u} := by
    simpa only [← orbitSize_mk] using (Nat.cast_pos.mpr (orbitSize_pos (histogram u)) :
      (0 : ℝ) < orbitSize (histogram u))
  have hn' : (0 : ℝ) < (Fintype.card I : ℝ)^Fintype.card I := pow_pos (Nat.cast_pos.mpr hn) _
  have hm := empirical_type_mass u
  have hr : (Fintype.card I : ℝ)^Fintype.card I ≤
      (((Fintype.card I+1)^Fintype.card A : ℕ) : ℝ) *
        ((Fintype.card {w : I → A // count w = count u} : ℝ) * ∏ a, (count u a : ℝ)^count u a) := by
    exact_mod_cast hm
  change _ ≤ (((Fintype.card I+1)^Fintype.card A : ℕ) : ℝ) *
    ((∏ a, (count u a : ℝ)^count u a) / (Fintype.card I : ℝ)^Fintype.card I)
  rw [← mul_div_assoc, le_div_iff₀ hn', inv_mul_eq_div, div_le_iff₀ ho]
  nlinarith [hr]
end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open scoped ComplexOrder
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

omit [DecidableEq I] in
lemma phaseFrame_sum_blocks :
    (∑ h : Histogram I A, phaseFrame h) = ∑ k : Histogram I A,
      (∑ h : Histogram I A, (histogramAmplitude h k : ℂ)^2) • block k := by
  simp_rw [phaseFrame_blocks]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_smul.symm

/- Constructive finite postselection before normalizing the histogram sum. -/
theorem phaseFrame_sum_domination (hn : 0 < Fintype.card I) :
    ((((Fintype.card I+1)^Fintype.card A : ℕ) : ℂ) •
      (∑ h : Histogram I A, phaseFrame h) - symProjector).PosSemidef := by
  let P : ℕ := (Fintype.card I+1)^Fintype.card A
  have hc (k : Histogram I A) :
      0 ≤ (P : ℝ) * (∑ h : Histogram I A, histogramAmplitude h k ^ 2) - (orbitSize k : ℝ)⁻¹ := by
    apply sub_nonneg.mpr
    apply (inverse_orbit_le_empirical hn k).trans
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun h _ => sq_nonneg (histogramAmplitude h k)) (Finset.mem_univ k))
      (Nat.cast_nonneg P)
  have he : (P : ℂ) • (∑ h : Histogram I A, phaseFrame h) - symProjector =
      ∑ k : Histogram I A,
        (((P : ℝ) * (∑ h : Histogram I A, histogramAmplitude h k ^ 2) -
          (orbitSize k : ℝ)⁻¹ : ℝ) : ℂ) • block k := by
    rw [phaseFrame_sum_blocks, symProjector, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul, ← sub_smul]
    congr 1
    push_cast
    rfl
  rw [show (((Fintype.card I+1)^Fintype.card A : ℕ) : ℂ) = (P : ℂ) from rfl, he]
  apply Matrix.posSemidef_sum
  intro k _
  exact (block_posSemidef k).smul (by exact_mod_cast hc k)

omit [DecidableEq I] in
lemma finiteMixture_posSemidef : (finiteMixture (I := I) (A := A)).PosSemidef := by
  exact (Matrix.posSemidef_sum _ (fun h _ => phaseFrame_posSemidef h)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/- Finite, normalized tensor postselection with explicit polynomial overhead.
Every product in finiteMixture comes from squared-norm-one empirical vectors;
there is no de Finetti theorem or independent density assumption. -/
theorem finite_postselection [Nonempty A] (hn : 0 < Fintype.card I) :
    ((((Fintype.card I+1)^(2*Fintype.card A) : ℕ) : ℂ) •
      (finiteMixture (I := I) (A := A)) - symProjector).PosSemidef := by
  let P : ℕ := (Fintype.card I+1)^Fintype.card A
  let H : ℕ := Fintype.card (Histogram I A)
  have hH : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  have h := phaseFrame_sum_domination (I := I) (A := A) hn
  have he : ((P*H : ℕ) : ℂ) • (finiteMixture (I := I) (A := A)) =
      (P : ℂ) • ∑ h : Histogram I A, phaseFrame h := by
    unfold finiteMixture
    rw [smul_smul, Nat.cast_mul]
    congr 1
    change (P : ℂ)*(H : ℂ)*(H : ℂ)⁻¹ = (P : ℂ)
    field_simp
  have hm : (P*H : ℕ) ≤ (Fintype.card I+1)^(2*Fintype.card A) := by
    have hle := Nat.mul_le_mul_left P (histogram_card_le (I := I) (A := A))
    simpa only [P,H,← pow_two,← pow_mul, mul_comm 2] using hle
  have hp : (0 : ℂ) ≤ (((Fintype.card I+1)^(2*Fintype.card A) : ℕ) : ℂ) - ((P*H : ℕ) : ℂ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hm)
  have hh := (finiteMixture_posSemidef (I := I) (A := A)).smul hp
  have hf := hh.add h
  rw [← he] at hf
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  module

end CoordinateSweeps.OrdinaryTensor

/- Positive-operator inequalities needed for the actual purification proof
of signed tensor density domination (05:eq13), not standalone main results. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.OrdinaryTensor
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma outer_trace_nonneg (v : (I → A) → ℂ) : 0 ≤ Matrix.trace (outer v) := by
  exact (outer_posSemidef v).trace_nonneg

/- The ordinary finite postselection theorem applied to an actual invariant
purification vector, rather than an assumed projection inequality. -/
theorem invariant_vector_postselection [Nonempty A] (hn : 0 < Fintype.card I)
    (v : (I → A) → ℂ) (hv : ∀ σ : Equiv.Perm I, ∀ w, v (permute σ w) = v w) :
    ((Matrix.trace (outer v) * ((Fintype.card I+1 : ℕ) : ℂ)^(2*Fintype.card A)) •
      finiteMixture - outer v).PosSemidef := by
  have hfix : symProjector.mulVec v = v := by
    apply symProjector_mulVec_of_constant
    intro u w he
    obtain ⟨σ,hσ⟩ := counts_eq_exists_perm he
    rw [← hσ,hv]
  have hPA : symProjector * outer v = outer v := by
    ext i j
    rw [Matrix.mul_apply]
    change (∑ k, symProjector i k * (v k * star (v j))) = v i * star (v j)
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    exact congrArg (fun z : ℂ => z*star (v j)) (congrFun hfix i)
  have h1 := PositiveTensor.projection_trace_domination (outer v) symProjector
    (outer_posSemidef v) symProjector_posSemidef.isHermitian symProjector_idempotent hPA
  have h2 := (finite_postselection (I := I) (A := A) hn).smul (outer_trace_nonneg v)
  have hh := h2.add h1
  simpa only [smul_sub,smul_smul,sub_add_sub_cancel,Nat.cast_pow] using hh
end CoordinateSweeps.OrdinaryTensor
namespace CoordinateSweeps.OrdinaryTensor
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

omit [DecidableEq I] in
lemma rawMixture_eq : rawMixture (I := I) (A := A) =
    ((Fintype.card (Histogram I A) : ℂ)*(Fintype.card (PhaseSpace I A) : ℂ)) • finiteMixture := by
  have hP : (Fintype.card (PhaseSpace I A) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr phaseSpace_card_pos.ne'
  by_cases hH : (Fintype.card (Histogram I A) : ℂ) = 0
  · have he : IsEmpty (Histogram I A) := Fintype.card_eq_zero_iff.mp (Nat.cast_eq_zero.mp hH)
    let := he
    simp [rawMixture,finiteMixture]
  · unfold finiteMixture phaseFrame rawMixture
    rw [smul_smul,← Finset.smul_sum,smul_smul]
    have hc : ((Fintype.card (Histogram I A) : ℂ)*(Fintype.card (PhaseSpace I A) : ℂ)) *
        (Fintype.card (Histogram I A) : ℂ)⁻¹ * (Fintype.card (PhaseSpace I A) : ℂ)⁻¹ = 1 := by field_simp
    rw [hc,one_smul]
omit [DecidableEq I] in
lemma rawMixture_domination [Nonempty A] :
    (rawMixture (I := I) (A := A) - finiteMixture).PosSemidef := by
  rw [rawMixture_eq]
  have hH : (1 : ℂ) ≤ (Fintype.card (Histogram I A) : ℂ) := by exact_mod_cast Fintype.card_pos
  have hP : (1 : ℂ) ≤ (Fintype.card (PhaseSpace I A) : ℂ) := by exact_mod_cast phaseSpace_card_pos
  have hp : (0 : ℂ) ≤ (Fintype.card (Histogram I A) : ℂ)*(Fintype.card (PhaseSpace I A) : ℂ)-1 :=
    sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le hH hP)
  simpa only [sub_smul,one_smul] using finiteMixture_posSemidef.smul hp
end CoordinateSweeps.OrdinaryTensor
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.SignedTensor_Domination
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

namespace CoordinateSweeps.SignedTensor
open PositiveTensor

/- Partial-trace invariance of the actual regrouping signs on each fixed
exception sector. No assumption of complex conditional probabilities occurs. -/
theorem partialTrace_regroup {p l : ℕ} (E : Finset (Fin l))
    (v : Word p l × Word p l → ℂ)
    (hv : ∀ u w, v (u,w) ≠ 0 → ∀ i,
      (odd (u i) ↔ ¬ odd (w i)) ↔ i ∈ E) :
    partialTrace (PositiveTensor.outer (fun uw => regroupPhase uw.1 uw.2 * v uw)) =
      partialTrace (PositiveTensor.outer v) := by
  ext u u'
  apply Finset.sum_congr rfl
  intro w _
  change (regroupPhase u w * v (u,w)) * star (regroupPhase u' w * v (u',w)) =
    v (u,w)*star (v (u',w))
  by_cases hu : v (u,w) = 0
  · simp [hu]
  by_cases hu' : v (u',w) = 0
  · simp [hu']
  have he : regroupPhase u w = regroupPhase u' w := by
    apply regroupPhase_of_same_parity
    intro i
    have hi := hv u w hu i
    have hi' := hv u' w hu' i
    tauto
  rw [star_mul,regroupPhase_star,he]
  calc
    _ = (regroupPhase u' w * regroupPhase u' w) * (v (u,w)*star (v (u',w))) := by ring
    _ = _ := by rw [regroupPhase_square,one_mul]

namespace ExceptionPattern
variable {p l : ℕ}

lemma encode_eq_some (F : ExceptionPattern p l) (a : Pair p) (i : Fin l) :
    F.encode a = some i ↔ ∃ hi : i ∈ F.sites, F.pair ⟨i,hi⟩ = a := by
  unfold encode
  split_ifs with h
  · constructor
    · intro he
      have hi := Option.some.inj he
      subst i
      exact ⟨(Classical.choose h).property, Classical.choose_spec h⟩
    · rintro ⟨hi,he⟩
      have hh : Classical.choose h = ⟨i,hi⟩ := F.injective ((Classical.choose_spec h).trans he.symm)
      rw [hh]
  · constructor
    · intro he; cases he
    · rintro ⟨hi,he⟩
      exact (h ⟨⟨i,hi⟩,he⟩).elim

lemma mem_sites_iff (F : ExceptionPattern p l) (i : Fin l) :
    i ∈ F.sites ↔ ∃ a, F.encode a = some i := by
  constructor
  · intro hi
    exact ⟨F.pair ⟨i,hi⟩,(F.encode_eq_some _ i).mpr ⟨hi,rfl⟩⟩
  · rintro ⟨a,ha⟩
    exact ((F.encode_eq_some a i).mp ha).choose

lemma encode_injective : Function.Injective (encode (p := p) (l := l)) := by
  intro F G he
  have hs : F.sites = G.sites := by
    ext i
    rw [F.mem_sites_iff,G.mem_sites_iff]
    simp only [he]
  cases F with | mk E f hf hfi =>
    cases G with | mk E' g hg hgi =>
      dsimp at hs
      subst E'
      have hp : f = g := by
        funext i
        have hh : (ExceptionPattern.mk E f hf hfi).encode (f i) = some i.val :=
          ((ExceptionPattern.mk E f hf hfi).encode_eq_some _ _).mpr ⟨i.property,rfl⟩
        rw [congrFun he (f i)] at hh
        obtain ⟨hi,hv⟩ := ((ExceptionPattern.mk E g hg hgi).encode_eq_some _ _).mp hh
        exact hv.symm
      subst g
      rfl

lemma card_le : Fintype.card (ExceptionPattern p l) ≤ (l+1)^((2*p)*(2*p)) := by
  have hc := Fintype.card_le_of_injective (encode (p := p) (l := l)) encode_injective
  simpa only [Fintype.card_fun,Fintype.card_option,Fintype.card_fin,
    Fintype.card_prod] using hc

lemma fillPair_at_pin (F : ExceptionPattern p l) (x : F.FreeWord) (i : F.sites) :
    F.fillPair x i.val = F.pair i := by simp [fillPair,i.property]

lemma fill_mismatch_iff (F : ExceptionPattern p l) (x : F.FreeWord) (i : Fin l) :
    (odd ((F.fill x).1 i) ↔ ¬ odd ((F.fill x).2 i)) ↔ i ∈ F.sites := by
  change (odd (F.fillPair x i).1 ↔ ¬ odd (F.fillPair x i).2) ↔ _
  by_cases hi : i ∈ F.sites
  · rw [show F.fillPair x i = F.pair ⟨i,hi⟩ from F.fillPair_at_pin x ⟨i,hi⟩]
    exact iff_of_true (F.mismatch ⟨i,hi⟩) hi
  · rw [show F.fillPair x i = (x ⟨i,hi⟩).val from F.fillPair_at_free x ⟨i,hi⟩]
    have hm := (x ⟨i,hi⟩).property
    tauto

lemma fill_disjoint {F G : ExceptionPattern p l} (x : F.FreeWord) (y : G.FreeWord)
    (he : F.fill x = G.fill y) : F = G := by
  have hs : F.sites = G.sites := by
    ext i
    rw [← F.fill_mismatch_iff x i,← G.fill_mismatch_iff y i,he]
  cases F with | mk E f hf hfi =>
    cases G with | mk E' g hg hgi =>
      dsimp at hs
      subst E'
      have hp : f = g := by
        funext i
        have hh : (ExceptionPattern.mk E f hf hfi).fillPair x i.val =
            (ExceptionPattern.mk E g hg hgi).fillPair y i.val :=
          Prod.ext (congrFun (congrArg Prod.fst he) i.val) (congrFun (congrArg Prod.snd he) i.val)
        simpa only [fillPair_at_pin] using hh
      subst g
      rfl

lemma entry_in_range (A : commutant p l) (u w : Word p l) (h : A.val u w ≠ 0) :
    ∃ x : (entryPattern A u w h).FreeWord, (entryPattern A u w h).fill x = (u,w) := by
  let F := entryPattern A u w h
  let x : F.FreeWord := fun i => ⟨(u i.val,w i.val),by
    have hi : i.val ∉ mismatchSlots u w := i.property
    have hm : ¬ (odd (u i.val) ↔ ¬ odd (w i.val)) := by
      simpa only [mismatchSlots,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    tauto⟩
  refine ⟨x,?_⟩
  have he (i : Fin l) : F.fillPair x i = (u i,w i) := by
    unfold fillPair
    split_ifs <;> rfl
  exact Prod.ext (funext fun i => congrArg Prod.fst (he i))
    (funext fun i => congrArg Prod.snd (he i))

/- Extend a permutation of the free slots by the identity on the exceptions. -/

lemma extendPerm_pin (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) (i : F.sites) :
    F.extendPerm σ i.val = i.val := by
  simp [extendPerm,Equiv.Perm.ofSubtype_apply_of_not_mem,i.property]

lemma extendPerm_free (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) (i : F.Free) :
    F.extendPerm σ i.val = (σ i).val := by
  exact Equiv.Perm.ofSubtype_apply_of_mem σ i.property

lemma fill_transport (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) (x : F.FreeWord) :
    F.fill (fun i => x (σ⁻¹ i)) =
      (wordPerm (F.extendPerm σ) (F.fill x).1, wordPerm (F.extendPerm σ) (F.fill x).2) := by
  have hinv : (F.extendPerm σ)⁻¹ = F.extendPerm σ⁻¹ := by
    simp only [extendPerm,map_inv]
  have he (i : Fin l) : F.fillPair (fun i => x (σ⁻¹ i)) i =
      F.fillPair x ((F.extendPerm σ)⁻¹ i) := by
    rw [hinv]
    by_cases hi : i ∈ F.sites
    · rw [show F.extendPerm σ⁻¹ i = i from F.extendPerm_pin σ⁻¹ ⟨i,hi⟩]
      simp [fillPair,hi]
    · rw [show F.extendPerm σ⁻¹ i = (σ⁻¹ ⟨i,hi⟩).val from F.extendPerm_free σ⁻¹ ⟨i,hi⟩]
      rw [show F.fillPair (fun i => x (σ⁻¹ i)) i = (x (σ⁻¹ ⟨i,hi⟩)).val from
        F.fillPair_at_free (fun i => x (σ⁻¹ i)) ⟨i,hi⟩,F.fillPair_at_free]
  exact Prod.ext (funext fun i => congrArg Prod.fst (he i))
    (funext fun i => congrArg Prod.snd (he i))

lemma purified_invariant (F : ExceptionPattern p l) (A : commutant p l)
    (σ : Equiv.Perm F.Free) (x : F.FreeWord) :
    F.purified A (fun i => x (σ⁻¹ i)) = F.purified A x := by
  unfold purified
  rw [F.fill_transport]
  apply regrouped_commutant_invariant
  intro i hi
  exact F.extendPerm_pin σ ⟨i,(F.fill_mismatch_iff x i).mp hi⟩

end ExceptionPattern
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

lemma component_image (F : ExceptionPattern p l) (A : commutant p l) (x : F.FreeWord) :
    F.component A (F.fill x) = A.val (F.fill x).1 (F.fill x).2 := by
  simp [component]

lemma purified_inclusion (F : ExceptionPattern p l) (A : commutant p l) :
    (inclusion F.embedding).mulVec (F.purified A) =
      fun q => regroupPhase q.1 q.2 * F.component A q := by
  funext q
  by_cases hq : q ∈ Set.range F.fill
  · obtain ⟨x,rfl⟩ := hq
    have hh := inclusion_mulVec_image F.embedding (F.purified A) x
    change (inclusion F.embedding).mulVec (F.purified A) (F.fill x) = _ at hh
    rw [hh,F.component_image]
    rfl
  · rw [inclusion_mulVec_notin F.embedding _ q hq]
    simp [component,hq]

lemma component_partialTrace (F : ExceptionPattern p l) (A : commutant p l) :
    partialTrace (PositiveTensor.outer ((inclusion F.embedding).mulVec (F.purified A))) =
      partialTrace (PositiveTensor.outer (F.component A)) := by
  rw [F.purified_inclusion]
  apply partialTrace_regroup F.sites
  intro u w h i
  have hq : (u,w) ∈ Set.range F.fill := by
    by_contra hn
    exact h (ite_eq_right hn)
  obtain ⟨x,hx⟩ := hq
  have he := F.fill_mismatch_iff x i
  simpa only [hx] using he

lemma component_sum (A : commutant p l) :
    ∑ F : ExceptionPattern p l, F.component A = fun q => A.val q.1 q.2 := by
  funext q
  rw [Finset.sum_apply]
  by_cases hq : A.val q.1 q.2 = 0
  · simp [component,hq]
  · let F := entryPattern A q.1 q.2 hq
    obtain ⟨x,hx⟩ := entry_in_range A q.1 q.2 hq
    have hmem : q ∈ Set.range F.fill := ⟨x,hx⟩
    rw [Finset.sum_eq_single F]
    · exact ite_eq_left hmem
    · intro G _ hG
      apply ite_eq_right
      rintro ⟨y,hy⟩
      exact hG (fill_disjoint y x (hy.trans hx.symm))
    · simp

lemma component_square_sum (A : commutant p l) (q : Word p l × Word p l) :
    ∑ F : ExceptionPattern p l, F.component A q * star (F.component A q) =
      A.val q.1 q.2 * star (A.val q.1 q.2) := by
  by_cases hq : A.val q.1 q.2 = 0
  · simp [component,hq]
  · let F := entryPattern A q.1 q.2 hq
    obtain ⟨x,hx⟩ := entry_in_range A q.1 q.2 hq
    have hmem : q ∈ Set.range F.fill := ⟨x,hx⟩
    rw [Finset.sum_eq_single F]
    · simp [component,hmem]
    · intro G _ hG
      have hn : q ∉ Set.range G.fill := by
        rintro ⟨y,hy⟩
        exact hG (fill_disjoint y x (hy.trans hx.symm))
      simp [component,hn]
    · simp

lemma purified_trace (F : ExceptionPattern p l) (A : commutant p l) :
    Matrix.trace (OrdinaryTensor.outer (F.purified A)) =
      Matrix.trace (PositiveTensor.outer (F.component A)) := by
  rw [show OrdinaryTensor.outer (F.purified A) = Matrix.vecMulVec (F.purified A) (star (F.purified A)) from rfl,
    ← inclusion_trace_outer F.embedding,F.purified_inclusion]
  apply Finset.sum_congr rfl
  intro q _
  change (regroupPhase q.1 q.2 * F.component A q) *
    star (regroupPhase q.1 q.2 * F.component A q) = F.component A q * star (F.component A q)
  rw [star_mul,regroupPhase_star]
  calc
    _ = (regroupPhase q.1 q.2 * regroupPhase q.1 q.2) * (F.component A q * star (F.component A q)) := by ring
    _ = _ := by rw [regroupPhase_square,one_mul]

lemma sum_purified_trace (A : commutant p l) :
    ∑ F : ExceptionPattern p l, Matrix.trace (OrdinaryTensor.outer (F.purified A)) =
      Matrix.trace (A.val*A.val.conjTranspose) := by
  simp_rw [purified_trace]
  simp only [PositiveTensor.outer,Matrix.trace,Matrix.diag_apply,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [Finset.sum_comm]
  simp_rw [component_square_sum]
  simp only [Fintype.sum_prod_type,Matrix.mul_apply,Matrix.conjTranspose_apply]
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}
lemma free_card_le (F : ExceptionPattern p l) : Fintype.card F.Free ≤ l := by
  rw [F.free_card]
  exact Nat.sub_le _ _

lemma matchedPair_nonempty (hp : 0 < p) : Nonempty (MatchedPair p) :=
  ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),Iff.rfl⟩⟩

/- Exact domination of a pinned component by a finite product mixture on its
free slots, after the proved sign cancellation in the genuine partial trace. -/
theorem component_postselection (F : ExceptionPattern p l) (hp : 0 < p)
    (hl : (2*p)*(2*p) < l) (A : commutant p l) :
    ((Matrix.trace (OrdinaryTensor.outer (F.purified A)) *
        ((Fintype.card F.Free+1 : ℕ) : ℂ)^(2*Fintype.card (MatchedPair p))) •
      partialTrace (inclusion F.embedding * (OrdinaryTensor.finiteMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose) -
      partialTrace (PositiveTensor.outer (F.component A))).PosSemidef := by
  let : Nonempty (MatchedPair p) := matchedPair_nonempty hp
  have h := OrdinaryTensor.invariant_vector_postselection (I := F.Free) (A := MatchedPair p) (F.free_card_pos hl)
    (F.purified A) (F.purified_invariant A)
  have hc := h.mul_mul_conjTranspose_same (inclusion F.embedding)
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] at hc
  have ho : inclusion F.embedding * OrdinaryTensor.outer (F.purified A) * (inclusion F.embedding).conjTranspose =
      PositiveTensor.outer ((inclusion F.embedding).mulVec (F.purified A)) :=
    mul_outer_mul_star _ _
  rw [ho] at hc
  have hp := partialTrace_posSemidef _ hc
  simpa only [partialTrace_sub,partialTrace_smul,F.component_partialTrace A] using hp
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor
variable {p : ℕ}

lemma basisDensity_posSemidef (a : Letter p) : (basisDensity a).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro b
  change (0 : ℂ) ≤ if b=a then _ else _
  split_ifs <;> norm_num

lemma basisDensity_le_one (a : Letter p) : (1-basisDensity a).PosSemidef := by
  have he : (1-basisDensity a) = Matrix.diagonal (fun b => if b=a then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hi : i=a <;> simp [basisDensity,Matrix.diagonal,hi]
    · simp [basisDensity,Matrix.diagonal,hij]

  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro b
  change (0 : ℂ) ≤ if b=a then _ else _
  split_ifs <;> norm_num

lemma pinAmplitude_density (a : Pair p) : pinAmplitude a * (pinAmplitude a).conjTranspose = basisDensity a.1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,pinAmplitude]
  rw [Finset.sum_eq_single a.2]
  · by_cases hi : i=a.1 <;> by_cases hj : j=a.1 <;>
      simp [Prod.ext_iff,hi,hj,basisDensity,Matrix.diagonal,eq_comm]
  · intro k _ hk
    simp [Prod.ext_iff,hk]
  · simp

lemma depolarized_free (s : ℕ) (r : EvenDensity p) :
    (depolarized s r - (keep s : ℂ) • r.val).PosSemidef := by
  simpa only [depolarized,add_sub_cancel_left] using
    (Matrix.PosSemidef.one (n := Letter p) (R := ℂ)).smul (by exact_mod_cast noise_nonneg s p)

lemma depolarized_pin (s : ℕ) (r : EvenDensity p) (a : Letter p) :
    (depolarized s r - (noise s p : ℂ) • basisDensity a).PosSemidef := by
  have ht : (0 : ℂ) ≤ (keep s : ℂ) := by exact_mod_cast keep_nonneg s
  have hu : (0 : ℂ) ≤ (noise s p : ℂ) := by exact_mod_cast noise_nonneg s p
  have h := (r.property.1.smul ht).add ((basisDensity_le_one a).smul hu)
  simpa only [depolarized,smul_sub,add_sub_assoc] using h
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}

lemma pinnedDensity_posSemidef (E : Finset (Fin l)) (a : E → Letter p) (r : EvenDensity p) :
    (pinnedDensity E a r).PosSemidef := by
  apply productMatrix_posSemidef
  intro i
  split_ifs with hi
  · exact basisDensity_posSemidef _
  · exact r.property.1

lemma keep_pow_lower (s n : ℕ) (hn : n ≤ s) : 1 ≤ (s+1 : ℝ) * (keep s)^n := by
  have hs : (0 : ℝ) < s+1 := by positivity
  have hi : (s+1 : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hs).mpr (by linarith [Nat.cast_nonneg (α := ℝ) s])
  have hb := one_add_mul_le_pow (a := -((s+1 : ℝ)⁻¹)) (by linarith : -2 ≤ -((s+1 : ℝ)⁻¹)) n
  have he : (1 - (s+1 : ℝ)⁻¹) = keep s := by unfold keep; field_simp; ring
  calc
    1 ≤ (s+1 : ℝ)-n := by
      have hn' : (n : ℝ) ≤ s := by exact_mod_cast hn
      linarith
    _ = (s+1 : ℝ)*(1+n * (-((s+1 : ℝ)⁻¹))) := by field_simp; ring
    _ ≤ (s+1 : ℝ)*(1+(-((s+1 : ℝ)⁻¹)))^n := mul_le_mul_of_nonneg_left hb hs.le
    _ = _ := by rw [show 1+(-((s+1 : ℝ)⁻¹)) = keep s from he]

lemma pin_coefficient_le (s p k : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hk : k ≤ (2*p)*(2*p)) :
    (s+1 : ℝ) * ((s+1 : ℝ)*(2*p))^k ≤ (s+1 : ℝ)^(13*p^2) := by
  have hs : (1 : ℝ) ≤ s+1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
  have hp' : (p : ℝ) ≤ s := by exact_mod_cast hps
  have ha : (2*p : ℝ) ≤ (s+1 : ℝ)^2 := by nlinarith [sq_nonneg (s : ℝ)]
  have hbase : (s+1 : ℝ)*(2*p) ≤ (s+1 : ℝ)^3 := by
    nlinarith [mul_le_mul_of_nonneg_left ha (by positivity : (0 : ℝ) ≤ s+1)]
  have hexp : 3*k+1 ≤ 13*p^2 := by
    have hp1 : 1 ≤ p*p := by nlinarith
    nlinarith [hk]
  calc
    _ ≤ (s+1 : ℝ) * ((s+1 : ℝ)^3)^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)
    _ = (s+1 : ℝ)^(3*k+1) := by rw [← pow_mul,pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ hs hexp

/- Each pinned ordinary product density is dominated by a tensor power of a
single even density, with only polynomial cost per actual exception. -/
theorem pinned_absorption (s : ℕ) (hp : 0 < p) (hls : l ≤ s)
    (E : Finset (Fin l)) (a : E → Letter p) (r : EvenDensity p) :
    (((s+1 : ℝ) * ((s+1 : ℝ)*(2*p))^E.card : ℝ) : ℂ) •
      densityPower l (depolarized s r) - pinnedDensity E a r |>.PosSemidef := by
  let c : Fin l → ℂ := fun i => if i ∈ E then (noise s p : ℂ) else (keep s : ℂ)
  let f : Fin l → Matrix (Letter p) (Letter p) ℂ :=
    fun i => if hi : i ∈ E then basisDensity (a ⟨i,hi⟩) else r.val
  have hlocal (i : Fin l) : (c i • f i).PosSemidef := by
    by_cases hi : i ∈ E
    · simpa only [c,f,ite_eq_left hi,dite_eq_left hi] using
        (basisDensity_posSemidef (a ⟨i,hi⟩)).smul (show (0 : ℂ) ≤ (noise s p : ℂ) by exact_mod_cast noise_nonneg s p)
    · simpa only [c,f,ite_eq_right hi,dite_eq_right hi] using
        r.property.1.smul (show (0 : ℂ) ≤ (keep s : ℂ) by exact_mod_cast keep_nonneg s)
  have hdiff (i : Fin l) : (depolarized s r - c i • f i).PosSemidef := by
    by_cases hi : i ∈ E
    · simpa only [c,f,ite_eq_left hi,dite_eq_left hi] using depolarized_pin s r (a ⟨i,hi⟩)
    · simpa only [c,f,ite_eq_right hi,dite_eq_right hi] using depolarized_free s r
  have h := productMatrix_mono (fun i => c i • f i) (fun _ => depolarized s r) hlocal hdiff
  rw [productMatrix_smul] at h
  have hc : (∏ i, c i) = ((keep s)^(l-E.card) * (noise s p)^E.card : ℝ) := by
    have hE : Finset.univ.filter (fun i : Fin l => i ∈ E) = E := by ext i; simp
    have hC : Finset.univ.filter (fun i : Fin l => i ∉ E) = Eᶜ := by ext i; simp
    simp only [c,Finset.prod_ite,hE,hC,Finset.prod_const,Finset.card_compl,Fintype.card_fin]
    push_cast
    ring
  rw [hc] at h
  let C : ℝ := (s+1 : ℝ) * ((s+1 : ℝ)*(2*p))^E.card
  have hC : (0 : ℝ) ≤ C := by dsimp [C]; positivity
  have hu : ((s+1 : ℝ)*(2*p))*noise s p = 1 := by
    have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    unfold noise
    field_simp
  have hCW : 1 ≤ C*((keep s)^(l-E.card)*(noise s p)^E.card) := by
    calc
      _ ≤ (s+1 : ℝ)*(keep s)^(l-E.card) := keep_pow_lower s _ (le_trans (Nat.sub_le _ _) hls)
      _ = _ := by
        dsimp [C]
        calc
          _ = ((s+1 : ℝ)*(keep s)^(l-E.card))*((((s+1 : ℝ)*(2*p))*noise s p)^E.card) := by rw [hu,one_pow,mul_one]
          _ = _ := by rw [mul_pow]; ring
  have hh := h.smul (show (0 : ℂ) ≤ (C : ℂ) by exact_mod_cast hC)
  have hz := (pinnedDensity_posSemidef E a r).smul
    (show (0 : ℂ) ≤ ((C*((keep s)^(l-E.card)*(noise s p)^E.card)-1 : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hCW)
  have ht := hh.add hz
  change ((C : ℂ) • (densityPower l (depolarized s r) -
    (((keep s)^(l-E.card)*(noise s p)^E.card : ℝ) : ℂ) • pinnedDensity E a r) +
    ((C*((keep s)^(l-E.card)*(noise s p)^E.card)-1 : ℝ) : ℂ) • pinnedDensity E a r).PosSemidef at ht
  change ((C : ℂ) • densityPower l (depolarized s r) - pinnedDensity E a r).PosSemidef
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  simp only [smul_sub,smul_smul,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one,
    sub_smul,one_smul]
  module
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}
theorem pinned_absorption_uniform (s : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (E : Finset (Fin l)) (hE : E.card ≤ (2*p)*(2*p)) (a : E → Letter p) (r : EvenDensity p) :
    ((((s+1 : ℝ)^(13*p^2)) : ℂ) • densityPower l (depolarized s r) - pinnedDensity E a r).PosSemidef := by
  have h := pinned_absorption s hp hls E a r
  have hle := pin_coefficient_le s p E.card hp hps hE
  have hr : (densityPower l (depolarized s r)).PosSemidef :=
    productMatrix_posSemidef (fun _ : Fin l => depolarized s r) (fun _ => depolarized_posSemidef s r)
  have hh := (hr.smul (show (0 : ℂ) ≤ (((s+1 : ℝ)^(13*p^2) -
    (s+1 : ℝ)*((s+1 : ℝ)*(2*p))^E.card : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hle)).add h
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  module
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

lemma siteAmplitude_pin (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (x : F.FreeWord) (i : F.sites) :
    F.siteAmplitude z i.val ((F.fill x).1 i.val) ((F.fill x).2 i.val) = 1 := by
  change F.siteAmplitude z i.val (F.fillPair x i.val).1 (F.fillPair x i.val).2 = 1
  rw [F.fillPair_at_pin]
  simp [siteAmplitude,i.property,pinAmplitude]

lemma siteAmplitude_free (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (x : F.FreeWord) (i : F.Free) :
    F.siteAmplitude z i.val ((F.fill x).1 i.val) ((F.fill x).2 i.val) = z (x i) := by
  change F.siteAmplitude z i.val (F.fillPair x i.val).1 (F.fillPair x i.val).2 = z (x i)
  rw [F.fillPair_at_free]
  simp [siteAmplitude,i.property,pairAmplitude,(x i).property]

lemma pairProduct_fill (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (x : F.FreeWord) :
    F.pairProduct z (F.fill x) = OrdinaryTensor.tensorVector z x := by
  unfold pairProduct
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ F.sites)]
  simp only [F.siteAmplitude_pin,F.siteAmplitude_free,Finset.prod_const_one,one_mul]
  rfl

lemma pairProduct_nonzero (F : ExceptionPattern p l) (z : MatchedPair p → ℂ)
    (q : Word p l × Word p l) (hq : F.pairProduct z q ≠ 0) : q ∈ Set.range F.fill := by
  have hi (i : Fin l) : F.siteAmplitude z i (q.1 i) (q.2 i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hq) i (Finset.mem_univ i)
  have hp (i : F.sites) : (q.1 i.val,q.2 i.val) = F.pair i := by
    by_contra hn
    exact hi i.val (by simp [siteAmplitude,i.property,pinAmplitude,hn])
  have hf (i : F.Free) : odd (q.1 i.val) ↔ odd (q.2 i.val) := by
    by_contra hn
    exact hi i.val (by simp [siteAmplitude,i.property,pairAmplitude,hn])
  let x : F.FreeWord := fun i => ⟨(q.1 i.val,q.2 i.val),hf i⟩
  have he (i : Fin l) : F.fillPair x i = (q.1 i,q.2 i) := by
    by_cases hi : i ∈ F.sites
    · exact (F.fillPair_at_pin x ⟨i,hi⟩).trans (hp ⟨i,hi⟩).symm
    · exact F.fillPair_at_free x ⟨i,hi⟩
  exact ⟨x,Prod.ext (funext fun i => congrArg Prod.fst (he i)) (funext fun i => congrArg Prod.snd (he i))⟩

lemma pairProduct_inclusion (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) :
    (inclusion F.embedding).mulVec (OrdinaryTensor.tensorVector z) = F.pairProduct z := by
  funext q
  by_cases hq : q ∈ Set.range F.fill
  · obtain ⟨x,rfl⟩ := hq
    have hh := inclusion_mulVec_image F.embedding (OrdinaryTensor.tensorVector z) x
    change (inclusion F.embedding).mulVec (OrdinaryTensor.tensorVector z) (F.fill x) = _ at hh
    exact hh.trans (F.pairProduct_fill z x).symm
  · rw [inclusion_mulVec_notin F.embedding _ q hq]
    exact (not_ne_iff.mp (fun hh => hq (F.pairProduct_nonzero z q hh))).symm

/- Partial tracing a filled product vector yields pinned basis densities at
the true exceptions and the same even density at every remaining slot. -/
lemma filled_product_partialTrace (F : ExceptionPattern p l) (z : MatchedPair p → ℂ)
    (hz : ∑ a, z a * star (z a) = 1) :
    partialTrace (PositiveTensor.outer ((inclusion F.embedding).mulVec (OrdinaryTensor.tensorVector z))) =
      pinnedDensity F.sites (fun i => (F.pair i).1) (pairDensity z hz) := by
  rw [F.pairProduct_inclusion]
  have he : partialTrace (PositiveTensor.outer (F.pairProduct z)) =
      productMatrix (fun i => F.siteAmplitude z i * (F.siteAmplitude z i).conjTranspose) := by
    ext u v
    simpa only [partialTrace,PositiveTensor.outer,Matrix.vecMulVec_apply,Pi.star_apply,pairProduct] using
      pair_product_partialTrace (F.siteAmplitude z) u v
  rw [he]
  congr 1
  funext i
  by_cases hi : i ∈ F.sites
  · simp only [siteAmplitude,hi,dite_eq_left,pinAmplitude_density]
  · simp [siteAmplitude,hi,pairDensity]
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

lemma purified_trace_le (F : ExceptionPattern p l) (A : commutant p l) :
    Matrix.trace (OrdinaryTensor.outer (F.purified A)) ≤ Matrix.trace (A.val*A.val.conjTranspose) := by
  rw [← sum_purified_trace A]
  exact Finset.single_le_sum (fun G _ => OrdinaryTensor.outer_trace_nonneg (G.purified A)) (Finset.mem_univ F)

lemma rawMixture_partialTrace (F : ExceptionPattern p l) (hn : 0 < Fintype.card F.Free) :
    partialTrace (inclusion F.embedding *
      (OrdinaryTensor.rawMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose) =
      F.rawPinned hn := by
  unfold OrdinaryTensor.rawMixture rawPinned
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_sum,Matrix.sum_mul,partialTrace_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro t _
  have he := congrArg (partialTrace (J := Word p l) (K := Word p l))
    (mul_outer_mul_star (inclusion F.embedding)
      (OrdinaryTensor.tensorVector (OrdinaryTensor.empiricalVector h t)))
  exact he.trans (F.filled_product_partialTrace _ (OrdinaryTensor.empiricalVector_unit hn h t))

lemma rawPinned_domination (F : ExceptionPattern p l) (hp : 0 < p) (hn : 0 < Fintype.card F.Free) :
    (F.rawPinned hn - partialTrace (inclusion F.embedding *
      (OrdinaryTensor.finiteMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose)).PosSemidef := by
  let : Nonempty (MatchedPair p) := matchedPair_nonempty hp
  have h := (OrdinaryTensor.rawMixture_domination (I := F.Free) (A := MatchedPair p)).mul_mul_conjTranspose_same (inclusion F.embedding)
  rw [Matrix.mul_sub,Matrix.sub_mul] at h
  have hh := partialTrace_posSemidef _ h
  simpa only [partialTrace_sub,F.rawMixture_partialTrace hn] using hh

lemma rawPinned_absorption (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p)
    (hps : p ≤ s) (hls : l ≤ s) (hn : 0 < Fintype.card F.Free) :
    ((((s+1 : ℝ)^(13*p^2)) : ℂ) • F.rawDensity s hp hn - F.rawPinned hn).PosSemidef := by
  have hh := Matrix.posSemidef_sum Finset.univ (fun d _ =>
    pinned_absorption_uniform s hp hps hls F.sites F.sites_card_le
      (fun i => (F.pair i).1) (F.dataDensity hn d))
  simpa only [Finset.sum_sub_distrib,← Finset.smul_sum,rawPinned,rawDensity,dataPoint,depolarizedDensity] using hh
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}

lemma matchedPair_card_le (p : ℕ) : Fintype.card (MatchedPair p) ≤ (2*p)*(2*p) := by
  simpa only [Pair,Fintype.card_prod,Letter,Fintype.card_fin] using
    (Fintype.card_subtype_le (fun a : Pair p => odd a.1 ↔ odd a.2))

namespace ExceptionPattern

lemma data_card_le (F : ExceptionPattern p l) : Fintype.card F.Data ≤ (l+1)^(8*p^2) := by
  have hh := OrdinaryTensor.histogram_card_le (I := F.Free) (A := MatchedPair p)
  have ht : Fintype.card (OrdinaryTensor.PhaseSpace F.Free (MatchedPair p)) =
      (Fintype.card F.Free+1)^Fintype.card (MatchedPair p) := by
    simp [OrdinaryTensor.PhaseSpace]
  rw [Fintype.card_prod,ht]
  calc
    _ ≤ (Fintype.card F.Free+1)^(2*Fintype.card (MatchedPair p)) := by
      rw [two_mul (Fintype.card (MatchedPair p)),pow_add]
      exact Nat.mul_le_mul_right _ hh
    _ ≤ (l+1)^(2*Fintype.card (MatchedPair p)) :=
      Nat.pow_le_pow_left (Nat.add_le_add_right F.free_card_le 1) _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith [matchedPair_card_le p])

lemma free_power_le (F : ExceptionPattern p l) (s : ℕ) (hls : l ≤ s) :
    (Fintype.card F.Free+1 : ℕ)^(2*Fintype.card (MatchedPair p)) ≤ (s+1)^(8*p^2) := by
  calc
    _ ≤ (s+1)^(2*Fintype.card (MatchedPair p)) :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (F.free_card_le.trans hls) 1) _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith [matchedPair_card_le p])

lemma component_uniform_domination (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p)
    (hps : p ≤ s) (hls : l ≤ s) (hl : (2*p)*(2*p) < l) (A : commutant p l) :
    ((Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(21*p^2)) •
      F.rawDensity s hp (F.free_card_pos hl) - partialTrace (PositiveTensor.outer (F.component A))).PosSemidef := by
  let hn := F.free_card_pos hl
  let M := partialTrace (inclusion F.embedding *
      (OrdinaryTensor.finiteMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose)
  have hM : M.PosSemidef := partialTrace_posSemidef _
    (OrdinaryTensor.finiteMixture_posSemidef.mul_mul_conjTranspose_same _)
  have ht : (0 : ℂ) ≤ Matrix.trace (A.val*A.val.conjTranspose) :=
    (Matrix.posSemidef_self_mul_conjTranspose A.val).trace_nonneg
  have ha : (0 : ℂ) ≤ Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(8*p^2) :=
    mul_nonneg ht (by positivity)
  have hc : Matrix.trace (OrdinaryTensor.outer (F.purified A)) *
      ((Fintype.card F.Free+1 : ℕ) : ℂ)^(2*Fintype.card (MatchedPair p)) ≤
      Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(8*p^2) := by
    exact mul_le_mul (F.purified_trace_le A) (by exact_mod_cast F.free_power_le s hls)
      (by positivity) ht
  have h₁ := domination_pad _ M _ _ hM hc (F.component_postselection hp hl A)
  have h₂ := domination_trans _ M (F.rawPinned hn) _ 1 ha h₁ (by
    simpa only [one_smul] using F.rawPinned_domination hp hn)
  rw [mul_one] at h₂
  have h₃ := domination_trans _ (F.rawPinned hn) (F.rawDensity s hp hn) _
    (((s+1 : ℝ)^(13*p^2)) : ℂ) ha h₂ (F.rawPinned_absorption s hp hps hls hn)
  convert h₃ using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  rw [mul_assoc,← pow_add]
  congr 2; ring
end ExceptionPattern

lemma densityProfile_card_le (p l : ℕ) : Fintype.card (DensityProfile p l) ≤ (l+1)^(12*p^2) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _F : ExceptionPattern p l, (l+1)^(8*p^2) :=
      Finset.sum_le_sum (fun F _ => F.data_card_le)
    _ = Fintype.card (ExceptionPattern p l) * (l+1)^(8*p^2) := by simp
    _ ≤ (l+1)^((2*p)*(2*p)) * (l+1)^(8*p^2) :=
      Nat.mul_le_mul_right _ (ExceptionPattern.card_le (p := p) (l := l))
    _ = _ := by rw [← pow_add]; congr 1; ring

lemma densityProfile_nonempty (hp : 0 < p) : Nonempty (DensityProfile p l) := by
  let : Nonempty (MatchedPair p) := ExceptionPattern.matchedPair_nonempty hp
  let F := ExceptionPattern.empty p l
  exact ⟨⟨F,Classical.choice inferInstance⟩⟩

lemma rawProfileDensity_eq (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l) :
    rawProfileDensity s p l hp hl = ∑ F : ExceptionPattern p l, F.rawDensity s hp (F.free_card_pos hl) := by
  exact Fintype.sum_sigma _

lemma rawProfileDensity_posSemidef (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l) :
    (rawProfileDensity s p l hp hl).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun d _ => densityPower_posSemidef _ _ (profilePoint s p l hp hl d).property.1)

/- Finite postselection for the literal signed action commutant. -/
theorem commutant_covariance_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hls : l ≤ s) (hl : (2*p)*(2*p) < l) (A : commutant p l) :
    ((Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(25*p^2)) •
      rawProfileDensity s p l hp hl - A.val*A.val.conjTranspose).PosSemidef := by
  have hc := partialTrace_posSemidef _ (outer_sum_domination (fun F : ExceptionPattern p l => F.component A))
  rw [ExceptionPattern.component_sum,partialTrace_sub,partialTrace_smul,partialTrace_sum,
    partialTrace_outer_matrix] at hc
  have hsum := Matrix.posSemidef_sum Finset.univ (fun (F : ExceptionPattern p l) _ =>
    F.component_uniform_domination s hp hps hls hl A)
  rw [Finset.sum_sub_distrib,← Finset.smul_sum,← rawProfileDensity_eq s p l hp hl] at hsum
  have h := domination_trans _ _ _ (Fintype.card (ExceptionPattern p l) : ℂ) _ (by positivity) hc hsum
  have hcard : Fintype.card (ExceptionPattern p l) ≤ (s+1)^(4*p^2) := by
    calc
      _ ≤ (l+1)^((2*p)*(2*p)) := ExceptionPattern.card_le (p := p) (l := l)
      _ ≤ (s+1)^((2*p)*(2*p)) := Nat.pow_le_pow_left (Nat.add_le_add_right hls 1) _
      _ = _ := by congr 1; ring
  apply domination_pad _ _ _ _ (rawProfileDensity_posSemidef s p l hp hl) _ h
  calc
    _ ≤ ((s+1 : ℕ) : ℂ)^(4*p^2) *
        (Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(21*p^2)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (Matrix.posSemidef_self_mul_conjTranspose _).trace_nonneg (by positivity))
    _ = _ := by rw [mul_left_comm,← pow_add]; congr 2; ring
end CoordinateSweeps.SignedTensor

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace CoordinateSweeps.SignedTensor
open PositiveTensor MeasureTheory

lemma isotypic_mem_commutant {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    isotypic (p := p) ρ ∈ commutant p l := by
  intro σ
  rw [isotypic_eq_projector]
  exact (ρ.projector_commute (action p l) σ).symm

lemma isotypic_self_mul {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    isotypic (p := p) ρ * (isotypic (p := p) ρ).conjTranspose = isotypic (p := p) ρ := by
  rw [(isotypic_posSemidef ρ).isHermitian.eq,isotypic_eq_projector,ρ.projector_idempotent]

lemma isotypic_trace_le (s p l : ℕ) (hls : l ≤ s) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Matrix.trace (isotypic (p := p) ρ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) := by
  rw [isotypic_trace]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh := (multiplicity_le p l ρ).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hls 1) _)
  have he : (2*p)*(2*p) = 4*p^2 := by ring
  rw [he] at hh
  exact_mod_cast hh

/- The large-slot case, as an actual probability mixture of even densities. -/

lemma densityPower_one (p l : ℕ) : densityPower l (1 : Matrix (Letter p) (Letter p) ℂ) = 1 := by
  ext u v
  by_cases huv : u=v
  · subst v
    simp [densityPower]
  · have hi : ∃ i, u i ≠ v i := Function.ne_iff.mp huv
    obtain ⟨i,hi⟩ := hi
    simp only [densityPower,Matrix.one_apply,ite_eq_right huv]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma densityPower_smul {p : ℕ} (l : ℕ) (c : ℂ) (r : Matrix (Letter p) (Letter p) ℂ) :
    densityPower l (c • r) = c^l • densityPower l r := by
  ext u v
  simp [densityPower,Finset.prod_mul_distrib]

lemma uniformDensity_power (p l : ℕ) (hp : 0 < p) :
    densityPower l (uniformDensity p hp).val = (((2*p : ℕ) : ℂ)^l)⁻¹ • 1 := by
  change densityPower l ((((2*p : ℕ) : ℂ)⁻¹) • 1) = _
  rw [densityPower_smul,densityPower_one,inv_pow]

lemma small_power_le (s p l : ℕ) (hps : p ≤ s) (hl : l ≤ (2*p)*(2*p)) :
    (2*p)^l ≤ (s+1)^(8*p^2) := by
  have hb : 2*p ≤ (s+1)^2 := by nlinarith
  calc
    _ ≤ ((s+1)^2)^l := Nat.pow_le_pow_left hb l
    _ = (s+1)^(2*l) := by rw [pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

/- Small slot counts, including zero, require no exceptional-sector chart. -/

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor

lemma finite_profile_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (hl : (2*p)*(2*p) < l) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    (((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) •
       ((Fintype.card (DensityProfile p l) : ℂ)⁻¹ • rawProfileDensity s p l hp hl) -
       isotypic (p := p) ρ).PosSemidef := by
  let : Nonempty (DensityProfile p l) := densityProfile_nonempty hp
  let A : commutant p l := ⟨isotypic ρ,isotypic_mem_commutant ρ⟩
  have h := commutant_covariance_domination s p l hp hps hls hl A
  change ((_ * _) • _ - isotypic ρ * (isotypic ρ).conjTranspose).PosSemidef at h
  simp only [A,isotypic_self_mul] at h
  have hcard : Fintype.card (DensityProfile p l) ≤ (s+1)^(12*p^2) :=
    (densityProfile_card_le p l).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hls 1) _)
  have hc0 : (Fintype.card (DensityProfile p l) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbig : ((s+1 : ℕ) : ℂ)^(12*p^2) * (Fintype.card (DensityProfile p l) : ℂ)⁻¹ ≥ 1 := by
    have hi : (0 : ℂ) ≤ (Fintype.card (DensityProfile p l) : ℂ)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_right (show (Fintype.card (DensityProfile p l) : ℂ) ≤
      ((s+1 : ℕ) : ℂ)^(12*p^2) by exact_mod_cast hcard) hi
    simpa only [mul_inv_cancel₀ hc0] using hh
  rw [smul_smul]
  apply domination_pad _ _ _ _ (rawProfileDensity_posSemidef s p l hp hl) _ h
  calc
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2)) * ((s+1 : ℕ) : ℂ)^(25*p^2) :=
      mul_le_mul_of_nonneg_right (isotypic_trace_le s p l hls ρ) (by positivity)
    _ = (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2) := by
      rw [mul_assoc,← pow_add]; congr 2; ring
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2)) *
        (((s+1 : ℕ) : ℂ)^(12*p^2) * (Fintype.card (DensityProfile p l) : ℂ)⁻¹) := by
      have hh := mul_le_mul_of_nonneg_left hbig
        (show (0 : ℂ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2) by positivity)
      simpa only [mul_one] using hh
    _ = _ := by
      rw [← mul_assoc,mul_assoc (ρ.dimension : ℂ),← pow_add]
      congr 3; ring

lemma finite_uniform_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (hl : l ≤ (2*p)*(2*p)) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    (((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(12*p^2)) •
      densityPower l (uniformDensity p hp).val-isotypic (p := p) ρ).PosSemidef := by
  rw [uniformDensity_power,smul_smul]
  have hP := trace_domination (isotypic (p := p) ρ) (isotypic_posSemidef ρ)
  apply domination_pad _ 1 _ _ Matrix.PosSemidef.one _ hP
  have hc0 : (((2*p : ℕ) : ℂ)^l) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hi : (0 : ℂ) ≤ (((2*p : ℕ) : ℂ)^l)⁻¹ := by positivity
  have hh := mul_le_mul_of_nonneg_right (show (((2*p : ℕ) : ℂ)^l) ≤
    ((s+1 : ℕ) : ℂ)^(8*p^2) by exact_mod_cast small_power_le s p l hps hl) hi
  rw [mul_inv_cancel₀ hc0] at hh
  calc
    _ ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) := isotypic_trace_le s p l hls ρ
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2)) *
        (((s+1 : ℕ) : ℂ)^(8*p^2)*(((2*p : ℕ) : ℂ)^l)⁻¹) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
        (show (0 : ℂ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) by positivity)
    _ = _ := by rw [← mul_assoc,mul_assoc (ρ.dimension : ℂ),← pow_add]; congr 3; ring

/- Finite (not a hypothetical measure) version of source05:eq13. -/
theorem finite_density_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    ∃ (I : Type) (_ : Fintype I) (_ : Nonempty I) (r : I → EvenDensity p),
      (((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) •
        ((Fintype.card I : ℂ)⁻¹ • ∑ i, densityPower l (r i).val)-isotypic (p := p) ρ).PosSemidef := by
  by_cases hl : (2*p)*(2*p)<l
  · exact ⟨DensityProfile p l,inferInstance,densityProfile_nonempty hp,
      profilePoint s p l hp hl,finite_profile_domination s p l hp hps hls hl ρ⟩
  · refine ⟨PUnit,inferInstance,inferInstance,fun _ => uniformDensity p hp,?_⟩
    simp only [Fintype.card_punit,Nat.cast_one,inv_one,Finset.univ_unique,Finset.sum_singleton,one_smul]
    apply domination_pad _ _ _ _ (densityPower_posSemidef _ _ (uniformDensity p hp).property.1) _
      (finite_uniform_domination s p l hp hps hls (by omega) ρ)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (show 0 < s+1 by omega) (show 12*p^2≤41*p^2 by omega)
end CoordinateSweeps.SignedTensor

end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.SignedTensor_Blocks
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

namespace CoordinateSweeps.SignedTensor
variable {B : Type} [Fintype B] [DecidableEq B]

/- Tensorization of finite density domination, preserving
finite probability normalization and the exact product of local dimensions. -/
theorem finite_block_density_domination (s p : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (l : B → ℕ) (hl : ∀ i, l i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (l i)))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (r : K → B → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(Fintype.card B*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x, DependentTensor.tensor (fun i => densityPower (l i) (r x i).val))-
          DependentTensor.tensor (fun i => isotypic (p := p) (ρ i))).PosSemidef := by
  choose K fK nK r hr using fun i => finite_density_domination s p (l i) hp hps (hl i) (ρ i)
  let : ∀ i, Fintype (K i) := fK
  let : ∀ i, Nonempty (K i) := nK
  refine ⟨(∀ i, K i),inferInstance,inferInstance,fun x i => r i (x i),?_⟩
  have hh := DependentTensor.tensor_mono
    (fun i => isotypic (p := p) (ρ i))
    (fun i => (((ρ i).dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) •
      ((Fintype.card (K i) : ℂ)⁻¹ • ∑ x, densityPower (l i) (r i x).val))
    (fun i => isotypic_posSemidef (ρ i)) hr
  rw [DependentTensor.tensor_smul] at hh
  have hm : DependentTensor.tensor (fun i => (Fintype.card (K i) : ℂ)⁻¹ •
      ∑ x, densityPower (l i) (r i x).val) =
      (Fintype.card (∀ i, K i) : ℂ)⁻¹ • ∑ x : ∀ i, K i,
        DependentTensor.tensor (fun i => densityPower (l i) (r i (x i)).val) := by
    simp only [Finset.smul_sum]
    rw [DependentTensor.tensor_mixture]
    rw [Fintype.card_pi,Nat.cast_prod,Finset.prod_inv_distrib]
  have hc : (∏ i, ((ρ i).dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) =
      (∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(Fintype.card B*(41*p^2)) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← pow_mul,mul_comm (41*p^2)]
  rwa [hm,hc] at hh

end CoordinateSweeps.SignedTensor

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.OrderedBlocks
variable {r : ℕ} (n : Fin r → ℕ)

lemma encode_lt_same {i : Fin r} (a b : Fin (n i)) :
    encode n ⟨i,a⟩ < encode n ⟨i,b⟩ ↔ a < b := by
  change offset n i+a.val < offset n i+b.val ↔ a.val < b.val
  omega

lemma positions_lt_of_block {i j : Fin r} (hij : i < j) (a : Fin (n i)) (b : Fin (n j)) :
    positions n ⟨i,a⟩ < positions n ⟨j,b⟩ := encode_lt_of_block n hij a b

lemma positions_lt_same {i : Fin r} (a b : Fin (n i)) :
    positions n ⟨i,a⟩ < positions n ⟨i,b⟩ ↔ a < b := encode_lt_same n a b

lemma perm_inv (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    (perm n σ)⁻¹=perm n (fun i => (σ i)⁻¹) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,j⟩,rfl⟩ := (positions n).surjective x
  apply (perm n σ).injective
  simp

end CoordinateSweeps.OrderedBlocks

namespace CoordinateSweeps.SignedTensor

lemma phase_double_prod {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) :
    phase σ w=∏ i : Fin l, ∏ j : Fin l,
      if j < i ∧ odd (w i) ∧ odd (w j) ∧ σ i < σ j then (-1 : ℂ) else 1 := by
  have he : Equiv.Perm.finPairsLT l=(Finset.univ : Finset ((i : Fin l) × Fin l)).filter (fun x => x.2 < x.1) := by
    ext x
    simp only [Equiv.Perm.mem_finPairsLT,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [phase_prod,he,Finset.prod_filter,Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs <;> simp_all

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks
variable {p r : ℕ} (n : Fin r → ℕ)

lemma prod_positions (f : Fin (∑ i, n i) → ℂ) :
    ∏ x, f x=∏ i, ∏ j : Fin (n i), f (positions n ⟨i,j⟩) := by
  rw [← Equiv.prod_comp (positions n) f,Fintype.prod_sigma]

lemma phase_grouped (σ : ∀ i, Equiv.Perm (Fin (n i))) (w : Word p (∑ i, n i)) :
    phase (perm n σ) w=∏ i, phase (σ i) (fun j => w (positions n ⟨i,j⟩)) := by
  rw [phase_double_prod,prod_positions n]
  apply Finset.prod_congr rfl
  intro i hi
  rw [phase_double_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [prod_positions n,Finset.prod_eq_single i]
  · apply Finset.prod_congr rfl
    intro b hb
    simp only [perm_apply,positions_lt_same]
  · intro j hj hji
    apply Finset.prod_eq_one
    intro b hb
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hn : ¬ positions n ⟨i,σ i a⟩ < positions n ⟨j,σ j b⟩ :=
        not_lt_of_ge (positions_lt_of_block n hlt _ _).le
      simp [hn]
    · have hn : ¬ positions n ⟨j,b⟩ < positions n ⟨i,a⟩ :=
        not_lt_of_ge (positions_lt_of_block n hgt _ _).le
      simp [hn]
  · simp

lemma groupWord_wordPerm (σ : ∀ i, Equiv.Perm (Fin (n i))) (w : Word p (∑ i, n i)) :
    groupWord n p (wordPerm (perm n σ) w)=fun i => wordPerm (σ i) (groupWord n p w i) := by
  funext i j
  simp [groupWord,wordPerm,perm_inv]

/- Genuine product-subgroup action, with no suppressed Koszul signs. -/
theorem matrix_grouped (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    matrix (p := p) (perm n σ)=
      Matrix.reindex (groupWord n p).symm (groupWord n p).symm
        (DependentTensor.tensor (fun i => matrix (σ i))) := by
  ext u w
  have he : u=wordPerm (perm n σ) w ↔
      ∀ i, groupWord n p u i=wordPerm (σ i) (groupWord n p w i) := by
    rw [← (groupWord n p).injective.eq_iff,groupWord_wordPerm]
    exact funext_iff
  change (if u=wordPerm (perm n σ) w then phase (perm n σ) w else 0)=
    ∏ i, if groupWord n p u i=wordPerm (σ i) (groupWord n p w i)
      then phase (σ i) (groupWord n p w i) else 0
  simp only [he]
  by_cases h : ∀ i, groupWord n p u i=wordPerm (σ i) (groupWord n p w i)
  · rw [ite_eq_left h,phase_grouped]
    simp only [h,ite_true]
    rfl
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r : ℕ} (n : Fin r → ℕ)

/- The subgroup operator is an actual group-algebra average on the full set
of slots, not an operator posited to factor. -/

lemma groupedAverage_factor {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    groupedAverage (p := p) n w g=
      Matrix.reindex (groupWord n p).symm (groupWord n p).symm
        (DependentTensor.tensor (fun i => averageMatrix (action p (n i)) (w i) (g i))) := by
  ext u v
  simp only [groupedAverage,averageMatrix,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_symm,DependentTensor.tensor,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  change (∑ ω : ∀ i, Ω i, (∏ i, w i (ω i))*
    matrix (perm n (fun i => g i (ω i))) u v)=
      ∏ i, ∑ ω : Ω i, w i ω*matrix (g i ω) (groupWord n p u i) (groupWord n p v i)
  have he (σ : ∀ i, Equiv.Perm (Fin (n i))) :
      matrix (perm n σ) u v=∏ i, matrix (σ i) (groupWord n p u i) (groupWord n p v i) := by
    have hh := congrArg (fun A : Matrix (Word p (∑ i, n i)) (Word p (∑ i, n i)) ℂ => A u v)
      (matrix_grouped (p := p) n σ)
    exact hh
  simp only [he]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  exact (Finset.prod_mul_distrib :
    (∏ i, w i (ω i)*matrix (g i (ω i)) (groupWord n p u i) (groupWord n p v i))=_).symm

lemma groupedProjector_factor (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    groupedProjector (p := p) n ρ=
      Matrix.reindex (groupWord n p).symm (groupWord n p).symm
        (DependentTensor.tensor (fun i => (ρ i).projector (action p (n i)))) := by
  exact groupedAverage_factor n _ _

lemma matrix_trace_reindex {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y)
    (A : Matrix X X ℂ) : Matrix.trace (Matrix.reindex e e A)=Matrix.trace A := by
  exact Equiv.sum_comp e.symm (fun i => A i i)

lemma reindex_moment {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (A : Matrix X X ℂ) (q : ℕ) :
    Matrix.trace ((((Matrix.reindexAlgEquiv ℂ ℂ e A).conjTranspose)*(Matrix.reindexAlgEquiv ℂ ℂ e A))^q)=
      Matrix.trace ((A.conjTranspose*A)^q) := by
  have hs : (Matrix.reindexAlgEquiv ℂ ℂ e A).conjTranspose=
      Matrix.reindexAlgEquiv ℂ ℂ e A.conjTranspose := by ext i j; rfl
  rw [hs,← map_mul,← map_pow]
  exact matrix_trace_reindex e _

/- Exact isotypic child moment factorization, including the true Hom
multiplicities and all zero-length blocks. -/
theorem grouped_projected_moment {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i)))
    {q : ℕ} (hq : q ≠ 0) :
    Matrix.trace (((groupedProjector (p := p) n ρ*groupedAverage n w g).conjTranspose*
      (groupedProjector n ρ*groupedAverage n w g))^q)=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (n i)))) : ℂ)*
        Matrix.trace (((averageMatrix (ρ i).matrix (w i) (g i)).conjTranspose*
          averageMatrix (ρ i).matrix (w i) (g i))^q) := by
  rw [groupedProjector_factor,groupedAverage_factor]
  let e := (groupWord n p).symm
  change Matrix.trace (((Matrix.reindexAlgEquiv ℂ ℂ e _*Matrix.reindexAlgEquiv ℂ ℂ e _).conjTranspose*
    (Matrix.reindexAlgEquiv ℂ ℂ e _*Matrix.reindexAlgEquiv ℂ ℂ e _))^q)=_
  rw [← map_mul,reindex_moment,← DependentTensor.tensor_mul,DependentTensor.tensor_moment]
  apply Finset.prod_congr rfl
  intro i hi
  exact (ρ i).projected_operator_moment _ (fun σ => (matrix_inv σ).symm) (w i) (g i) hq

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p : ℕ}

lemma isEven_iff_commute (A : Matrix (Letter p) (Letter p) ℂ) :
    IsEven A ↔ Commute A (grading p) := by
  constructor
  · intro h
    show A*grading p=grading p*A
    ext i j
    simp only [grading,Matrix.mul_diagonal,Matrix.diagonal_mul]
    by_cases hi : odd i
    · by_cases hj : odd j
      · simp [hi,hj]
      · simp [hi,hj,h i j (by tauto)]
    · by_cases hj : odd j
      · simp [hi,hj,h i j (by tauto)]
      · simp [hi,hj]
  · intro h i j hij
    have hh := congrArg (fun M : Matrix (Letter p) (Letter p) ℂ => M i j) h.eq
    simp only [grading,Matrix.mul_diagonal,Matrix.diagonal_mul] at hh
    by_cases hi : odd i
    · have hj : ¬ odd j := hij.mp hi
      simpa [hi,hj] using hh.symm
    · have hj : odd j := by tauto
      simpa [hi,hj] using hh

lemma isEven_add {A B : Matrix (Letter p) (Letter p) ℂ} (hA : IsEven A) (hB : IsEven B) :
    IsEven (A+B) := by intro i j hij; simp only [Matrix.add_apply,hA i j hij,hB i j hij,add_zero]

lemma isEven_smul (c : ℂ) {A : Matrix (Letter p) (Letter p) ℂ} (hA : IsEven A) :
    IsEven (c • A) := by intro i j hij; simp only [Matrix.smul_apply,smul_eq_mul,hA i j hij,mul_zero]

lemma isEven_sum {I : Type*} [Fintype I] (A : I → Matrix (Letter p) (Letter p) ℂ)
    (hA : ∀ i, IsEven (A i)) : IsEven (∑ i, A i) := by
  intro i j hij
  simp only [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun a _ => hA a i j hij)

lemma isEven_one : IsEven (1 : Matrix (Letter p) (Letter p) ℂ) := by
  intro i j hij
  apply Matrix.one_apply_ne
  intro he
  subst j
  tauto

lemma densityPower_commute_of_even {l : ℕ} (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : IsEven r) (σ : Equiv.Perm (Fin l)) :
    matrix σ*densityPower l r=densityPower l r*matrix σ := by
  have hpar {u w : Word p l} (h : densityPower l r u w ≠ 0) :
      ∀ i, odd (u i) ↔ odd (w i) := by
    intro i
    have he : r (u i) (w i) ≠ 0 := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ _)
    by_contra hn
    exact he (hr _ _ (by tauto))
  ext u w
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single ((wordPerm σ).symm u),Finset.sum_eq_single (wordPerm σ w)]
  · simp only [(wordPerm σ).apply_symm_apply,ite_true]
    have hd : densityPower l r u (wordPerm σ w)=densityPower l r ((wordPerm σ).symm u) w := by
      simpa using densityPower_permute σ r ((wordPerm σ).symm u) w
    rw [hd]
    by_cases hn : densityPower l r ((wordPerm σ).symm u) w=0
    · simp [hn]
    · rw [phase_eq_of_parity σ _ _ (hpar hn),mul_comm]
  · intro v hv hne; simp [hne]
  · simp
  · intro v hv hne
    have hh : u ≠ wordPerm σ v := by
      intro he
      exact hne ((Equiv.eq_symm_apply _).mpr he.symm)
    simp [hh]
  · simp

lemma densityPower_commute_lift {l : ℕ} (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : IsEven r) (x : MonoidAlgebra ℂ (Equiv.Perm (Fin l))) :
    (MonoidAlgebra.lift ℂ _ _ (action p l) x)*densityPower l r =
      densityPower l r*(MonoidAlgebra.lift ℂ _ _ (action p l) x) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa [action] using densityPower_commute_of_even r hr g
  | add x y hx hy => simp only [map_add,add_mul,mul_add,hx,hy]
  | smul c x hx => simp only [map_smul,smul_mul_assoc,mul_smul_comm,hx]

/- Constructed even whitening of the regularized empirical row density. -/
theorem exists_even_whitening {R : Type*} [Fintype R] [Nonempty R]
    (r : R → EvenDensity p) {ε : ℝ} (hε : 0 < ε) :
    let B := (Fintype.card R : ℂ)⁻¹ • ∑ i, (r i).val + (ε : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)
    ∃ A : Matrix (Letter p) (Letter p) ℂ, A.PosSemidef ∧ IsEven A ∧ A*B*A=1 ∧
      ((Fintype.card R : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)-
        ∑ i, A*(r i).val*A).PosSemidef := by
  dsimp only
  let B := (Fintype.card R : ℂ)⁻¹ • ∑ i, (r i).val + (ε : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)
  have hBp : B.PosDef := TensorBoard.average_regularization_posDef (fun i => (r i).val)
    (fun i => (r i).property.1) hε
  have hBe : IsEven B := isEven_add (isEven_smul _ (isEven_sum _ (fun i => (r i).property.2.2)))
    (isEven_smul _ isEven_one)
  obtain ⟨A,hA,hABA,hcomm⟩ := TensorBoard.exists_whitening B hBp
  refine ⟨A,hA,(isEven_iff_commute A).mpr (hcomm _ ((isEven_iff_commute B).mp hBe)),hABA,?_⟩
  apply TensorBoard.whitening_sum_bound _ B A hA.isHermitian hABA
  dsimp [B]
  convert (Matrix.PosSemidef.one (n := Letter p) (R := ℂ)).smul hε.le using 1
  all_goals try with_reducible_and_instances rfl
  module

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p l : ℕ}

/- Even inhomogeneous site tensors transform by the *signed* permutation
matrix with no residual phase. This is what permits regrouping deleted rows
and columns without identifying the two Koszul charts by an unsigned map. -/
lemma tensor_covariance (A : Fin l → Matrix (Letter p) (Letter p) ℂ)
    (hA : ∀ i, IsEven (A i)) (σ : Equiv.Perm (Fin l)) :
    matrix σ*TensorBoard.tensor A=
      TensorBoard.tensor (fun i => A (σ⁻¹ i))*matrix σ := by
  have hpar {u w : Word p l} (h : TensorBoard.tensor A u w ≠ 0) :
      ∀ i, odd (u i) ↔ odd (w i) := by
    intro i
    have he : A i (u i) (w i) ≠ 0 := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ _)
    by_contra hn
    exact he (hA i _ _ (by tauto))
  ext u w
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single ((wordPerm σ).symm u),Finset.sum_eq_single (wordPerm σ w)]
  · simp only [(wordPerm σ).apply_symm_apply,ite_true]
    have hd : TensorBoard.tensor (fun i => A (σ⁻¹ i)) u (wordPerm σ w)=
        TensorBoard.tensor A ((wordPerm σ).symm u) w := by
      change (∏ i, A (σ⁻¹ i) (u i) (w (σ⁻¹ i)))=∏ i, A i (u (σ i)) (w i)
      simpa using (Equiv.prod_comp σ (fun i => A (σ⁻¹ i) (u i) (w (σ⁻¹ i)))).symm
    rw [hd]
    by_cases hn : TensorBoard.tensor A ((wordPerm σ).symm u) w=0
    · simp [hn]
    · rw [phase_eq_of_parity σ _ _ (hpar hn),mul_comm]
  · intro v hv hne; simp [hne]
  · simp
  · intro v hv hne
    have hh : u ≠ wordPerm σ v := by
      intro he
      exact hne ((Equiv.eq_symm_apply _).mpr he.symm)
    simp [hh]
  · simp

lemma tensor_signed_conjugate (A : Fin l → Matrix (Letter p) (Letter p) ℂ)
    (hA : ∀ i, IsEven (A i)) (σ : Equiv.Perm (Fin l)) :
    matrix σ*TensorBoard.tensor A*(matrix σ).conjTranspose=
      TensorBoard.tensor (fun i => A (σ⁻¹ i)) := by
  rw [tensor_covariance A hA σ,mul_assoc,← matrix_inv,← matrix_mul,mul_inv_cancel,matrix_one,mul_one]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks
variable {p r : ℕ} (n : Fin r → ℕ)

lemma grouped_densityPower (a : Fin r → EvenDensity p) :
    (DependentTensor.tensor (fun i => densityPower (n i) (a i).val)).submatrix
      (groupWord n p) (groupWord n p)=TensorBoard.tensor (fun k => (groupedSite n a k).val) := by
  ext u v
  change (∏ i, ∏ j : Fin (n i), (a i).val (u (positions n ⟨i,j⟩)) (v (positions n ⟨i,j⟩)))=
    ∏ k, (a ((positions n).symm k).1).val (u k) (v k)
  rw [prod_positions]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [Equiv.symm_apply_apply]

/- Literal contiguous-block projectors are dominated by independent finite
mixtures of even site densities, with all local dimension factors. -/
theorem finite_grouped_density_domination (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hn : ∀ i, n i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (groupedSite n (a x) k).val))-
          groupedProjector (p := p) n ρ).PosSemidef := by
  obtain ⟨K,hK,nK,a,ha⟩ := finite_block_density_domination s p hp hps n hn ρ
  let := hK
  let := nK
  refine ⟨K,hK,nK,a,?_⟩
  have hh := ha.submatrix (groupWord n p)
  have hm : (∑ x, DependentTensor.tensor (fun i => densityPower (n i) (a x i).val)).submatrix
      (groupWord n p) (groupWord n p)=∑ x, TensorBoard.tensor (fun k => (groupedSite n (a x) k).val) := by
    ext u v
    simp only [Matrix.submatrix_apply,Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    exact congrArg (fun M => M u v) (grouped_densityPower n (a x))
  simp only [Fintype.card_fin,Matrix.submatrix_sub,Matrix.submatrix_smul,
    Pi.sub_apply,Pi.smul_apply,hm] at hh
  have he : (DependentTensor.tensor (fun i => isotypic (p := p) (ρ i))).submatrix
      (groupWord n p) (groupWord n p)=groupedProjector (p := p) n ρ := by
    simp only [groupedProjector_factor,isotypic_eq_projector]
    rfl
  rwa [he] at hh

/- The same domination after an arbitrary *signed* change of slot chart. -/
theorem finite_regrouped_density_domination (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hn : ∀ i, n i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (σ : Equiv.Perm (Fin (∑ i, n i))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (groupedSite n (a x) (σ⁻¹ k)).val))-
          matrix σ*groupedProjector (p := p) n ρ*(matrix σ).conjTranspose).PosSemidef := by
  obtain ⟨K,hK,nK,a,ha⟩ := finite_grouped_density_domination n s hp hps hn ρ
  let := hK
  let := nK
  refine ⟨K,hK,nK,a,?_⟩
  have hh := ha.mul_mul_conjTranspose_same (matrix σ)
  simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul] at hh
  have ht (x : K) : matrix σ*TensorBoard.tensor (fun k => (groupedSite n (a x) k).val)*(matrix σ).conjTranspose=
      TensorBoard.tensor (fun k => (groupedSite n (a x) (σ⁻¹ k)).val) :=
    tensor_signed_conjugate _ (fun k => (groupedSite n (a x) k).property.2.2) σ
  simpa only [ht] using hh

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} (n : Fin r → ℕ)

lemma groupedProjector_posSemidef (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    (groupedProjector (p := p) n ρ).PosSemidef := by
  rw [groupedProjector_factor]
  exact (DependentTensor.tensor_posSemidef _ (fun i => (ρ i).projector_posSemidef _
    (fun σ => (matrix_inv σ).symm))).submatrix _

lemma groupedProjector_idempotent (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    groupedProjector (p := p) n ρ*groupedProjector n ρ=groupedProjector n ρ := by
  rw [groupedProjector_factor]
  change Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _*
    Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _=Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _
  rw [← map_mul,← DependentTensor.tensor_mul]
  simp only [UnitaryIrrep.projector_idempotent]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)

lemma ambientProjectorAlgebra_lift (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    MonoidAlgebra.lift ℂ _ _ (action p l) (ambientProjectorAlgebra n h σ ρ)=
      ambientProjector (p := p) n h σ ρ := by
  subst l
  simp only [ambientProjectorAlgebra,lift_averageAlgebra,averageMatrix,ambientProjector,
    lengthMatrix,groupedProjector,groupedAverage,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  change matrix (σ*(Equiv.permCongr (finCongr rfl) (perm n ω))*σ⁻¹)=_
  simp only [finCongr_refl,matrix_mul,matrix_inv]
  rfl

lemma ambientProjector_posSemidef (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    (ambientProjector (p := p) n h σ ρ).PosSemidef := by
  subst l
  exact (groupedProjector_posSemidef n ρ).mul_mul_conjTranspose_same (matrix σ)

lemma ambientProjector_idempotent (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    ambientProjector (p := p) n h σ ρ*ambientProjector n h σ ρ=ambientProjector n h σ ρ := by
  subst l
  unfold ambientProjector lengthMatrix
  calc
    _ = matrix σ*(groupedProjector n ρ*((matrix σ).conjTranspose*matrix σ)*groupedProjector n ρ)*
      (matrix (p := p) σ).conjTranspose := by noncomm_ring
    _ = _ := by rw [matrix_unitary,mul_one,groupedProjector_idempotent]

/- Actual ambient projectors, not hypothesized density mixtures. -/
theorem finite_ambient_density_domination (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hn : ∀ i, n i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l)) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (groupedSite n (a x) ((finCongr h).symm (σ⁻¹ k))).val))-
          ambientProjector (p := p) n h σ ρ).PosSemidef := by
  subst l
  simpa [ambientProjector,lengthMatrix] using
    finite_regrouped_density_domination n s hp hps hn ρ σ

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)

lemma ambientAverage_factor (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    ambientAverage (p := p) n h σ w g=
      matrix σ*lengthMatrix h (groupedAverage n w g)*(matrix σ).conjTranspose := by
  subst l
  simp only [ambientAverage,averageMatrix,groupedAverage,lengthMatrix,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  change matrix (σ*Equiv.permCongr (finCongr rfl) (perm n (fun i => g i (ω i)))*σ⁻¹)=_
  simp only [finCongr_refl,matrix_mul,matrix_inv]
  rfl

lemma matrix_unitary_reverse (σ : Equiv.Perm (Fin l)) :
    matrix (p := p) σ*(matrix σ).conjTranspose=1 := by
  rw [← matrix_inv,← matrix_mul,mul_inv_cancel,matrix_one]

lemma conjugate_mul {X : Type*} [Fintype X] [DecidableEq X]
    (U A B : Matrix X X ℂ) (hU : U.conjTranspose*U=1) :
    (U*A*U.conjTranspose)*(U*B*U.conjTranspose)=U*(A*B)*U.conjTranspose := by
  calc
    _ = U*A*(U.conjTranspose*U)*B*U.conjTranspose := by noncomm_ring
    _ = _ := by rw [hU,mul_one]; noncomm_ring

lemma conjugate_pow {X : Type*} [Fintype X] [DecidableEq X]
    (U A : Matrix X X ℂ) (hU : U.conjTranspose*U=1) (hU' : U*U.conjTranspose=1) (q : ℕ) :
    (U*A*U.conjTranspose)^q=U*A^q*U.conjTranspose := by
  induction q with
  | zero => simpa using hU'.symm
  | succ q ih => rw [pow_succ,ih,conjugate_mul U _ _ hU,pow_succ]

lemma conjugate_moment {X : Type*} [Fintype X] [DecidableEq X]
    (U A : Matrix X X ℂ) (hU : U.conjTranspose*U=1) (hU' : U*U.conjTranspose=1) (q : ℕ) :
    Matrix.trace (((U*A*U.conjTranspose).conjTranspose*(U*A*U.conjTranspose))^q)=
      Matrix.trace ((A.conjTranspose*A)^q) := by
  have hs : (U*A*U.conjTranspose).conjTranspose=U*A.conjTranspose*U.conjTranspose := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  rw [hs,conjugate_mul U _ _ hU,conjugate_pow U _ hU hU']
  rw [Matrix.trace_mul_cycle,hU,one_mul]

/- The child moment formula survives the literal slot chart, with actual Hom multiplicities. -/
theorem ambient_projected_moment (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i)))
    {q : ℕ} (hq : q ≠ 0) :
    Matrix.trace (((ambientProjector (p := p) n h σ ρ*ambientAverage n h σ w g).conjTranspose*
      (ambientProjector n h σ ρ*ambientAverage n h σ w g))^q)=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (n i)))) : ℂ)*
        Matrix.trace (((averageMatrix (ρ i).matrix (w i) (g i)).conjTranspose*
          averageMatrix (ρ i).matrix (w i) (g i))^q) := by
  subst l
  rw [ambientAverage_factor]
  unfold ambientProjector lengthMatrix
  rw [conjugate_mul _ _ _ (matrix_unitary σ),conjugate_moment _ _
    (matrix_unitary σ) (matrix_unitary_reverse σ)]
  exact grouped_projected_moment n ρ w g hq

end CoordinateSweeps.SignedTensor

/-!
All definitions are finite and use ordinary probability and trace normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.FiberBlocks
open OrderedBlocks
variable {L : Type*} [Fintype L] {r : ℕ} (f : L → Fin r)

lemma label_slots (k : Fin (∑ i, size f i)) :
    f (slots f k)=((positions (size f)).symm k).1 := by
  exact (cards f ((positions (size f)).symm k).1 ((positions (size f)).symm k).2).property

/- The same chart with the literal cardinal as ambient length. -/

lemma label_regroup (e : Fin (Fintype.card L) ≃ L) (k : Fin (Fintype.card L)) :
    ((positions (size f)).symm ((finCongr (total f)).symm ((regroup f e)⁻¹ k))).1=f (e k) := by
  have he : slots f ((finCongr (total f)).symm ((regroup f e)⁻¹ k))=e k := by
    change chart f ((regroup f e).symm k)=e k
    simp [regroup]
  rw [← label_slots f,he]

end CoordinateSweeps.FiberBlocks

namespace CoordinateSweeps.FiberBlocks
open OrderedBlocks
variable {L : Type*} [Fintype L] {r : ℕ} (f : L → Fin r)

lemma slots_positions (i : Fin r) (j : Fin (size f i)) :
    slots f (positions (size f) ⟨i,j⟩)=(cards f i j).val := by
  simp [slots]

/- Independent permutations of the actual fibers, on the literal ambient set. -/

lemma action_apply (σ : ∀ i, Equiv.Perm (Fin (size f i))) (i : Fin r) (j : Fin (size f i)) :
    action f σ (cards f i j).val=(cards f i (σ i j)).val := by
  rw [← slots_positions f i j,← slots_positions f i (σ i j)]
  change slots f (perm (size f) σ ((slots f).symm (slots f (positions (size f) ⟨i,j⟩))))=_
  rw [Equiv.symm_apply_apply,perm_apply]

lemma ambient_action (e : Fin (Fintype.card L) ≃ L)
    (σ : ∀ i, Equiv.Perm (Fin (size f i))) :
    Equiv.permCongr e.symm (action f σ)=
      regroup f e*Equiv.permCongr (finCongr (total f)) (perm (size f) σ)*(regroup f e)⁻¹ := by
  apply Equiv.ext
  intro x
  change e.symm (slots f (perm (size f) σ ((slots f).symm (e x))))=_
  simp only [Equiv.Perm.mul_apply,Equiv.permCongr_apply,regroup,chart,
    Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.Perm.coe_inv]
  simp

/- A label-preserving permutation has genuine induced local permutations. -/

lemma restrict_apply (σ : Equiv.Perm L) (hσ : ∀ x, f (σ x)=f x)
    (i : Fin r) (j : Fin (size f i)) :
    (cards f i (restrict f σ hσ i j)).val=σ (cards f i j).val := by
  simp [restrict,Equiv.permCongr_apply]

lemma action_restrict (σ : Equiv.Perm L) (hσ : ∀ x, f (σ x)=f x) :
    action f (restrict f σ hσ)=σ := by
  apply Equiv.ext
  intro x
  let i := f x
  let j := (cards f i).symm ⟨x,rfl⟩
  have hx : (cards f i j).val=x := congrArg Subtype.val ((cards f i).apply_symm_apply ⟨x,rfl⟩)
  rw [← hx,action_apply,restrict_apply]

end CoordinateSweeps.FiberBlocks
namespace CoordinateSweeps.SignedTensor
open UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)
lemma groupedProjector_commute_average {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    groupedProjector (p := p) n ρ*groupedAverage n w g=groupedAverage n w g*groupedProjector n ρ := by
  rw [groupedProjector_factor,groupedAverage_factor]
  change Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _*
      Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _=
    Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _*
      Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _
  rw [← map_mul,← map_mul,← DependentTensor.tensor_mul,← DependentTensor.tensor_mul]
  congr 1
  apply congrArg DependentTensor.tensor
  funext i
  simp only [averageMatrix,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro ω _
  exact congrArg (fun A => w i ω • A) ((ρ i).projector_commute (action p (n i)) (g i ω)).symm

lemma ambientProjector_commute_average (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    ambientProjector (p := p) n h σ ρ*ambientAverage n h σ w g=
      ambientAverage n h σ w g*ambientProjector n h σ ρ := by
  subst l
  rw [ambientAverage_factor]
  unfold ambientProjector lengthMatrix
  rw [conjugate_mul _ _ _ (matrix_unitary σ),conjugate_mul _ _ _ (matrix_unitary σ)]
  rw [groupedProjector_commute_average]
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open UnitaryIrrep
variable {p r : ℕ} (n : Fin r → ℕ)
lemma child_product_bound (s : ℕ) (hn : ∀ i, n i ≤ s)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) (T E : Fin r → ℝ)
    (hT : ∀ i, 0 ≤ T i) (hE : ∀ i, T i ≤ Real.exp (E i)) :
    (∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
      (matrixRepresentation (action p (n i)))) : ℝ)*T i) ≤
        ((s+1 : ℕ) : ℝ)^(r*((2*p)*(2*p)))*Real.exp (∑ i, E i) := by
  rw [Finset.prod_mul_distrib]
  have hm : (∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
      (matrixRepresentation (action p (n i)))) : ℝ)) ≤ ((s+1 : ℕ) : ℝ)^(r*((2*p)*(2*p))) := by
    calc
      _ ≤ ∏ _ : Fin r, ((s+1 : ℕ) : ℝ)^((2*p)*(2*p)) := Finset.prod_le_prod
        (fun _ _ => Nat.cast_nonneg _) (fun i _ => by
          exact_mod_cast (multiplicity_le p (n i) (ρ i)).trans
            (Nat.pow_le_pow_left (Nat.add_le_add_right (hn i) 1) _))
      _ = _ := by rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul,Nat.mul_comm]
  have ht : (∏ i, T i) ≤ Real.exp (∑ i, E i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => hT i) (fun i _ => hE i)
  exact mul_le_mul hm ht (Finset.prod_nonneg (fun i _ => hT i)) (by positivity)
end CoordinateSweeps.SignedTensor
namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} {L : Type*} [Fintype L] (f : L → Fin r)

lemma fiberProjectorAlgebra_lift (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    MonoidAlgebra.lift ℂ _ _ (action p (Fintype.card L)) (fiberProjectorAlgebra f e ρ)=
      fiberProjector (p := p) f e ρ := ambientProjectorAlgebra_lift _ _ _ _

lemma fiberProjector_posSemidef (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    (fiberProjector (p := p) f e ρ).PosSemidef := ambientProjector_posSemidef _ _ _ _

lemma fiberProjector_idempotent (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    fiberProjector (p := p) f e ρ*fiberProjector f e ρ=fiberProjector f e ρ :=
  ambientProjector_idempotent _ _ _ _

/- Exact regrouping connects local isotypic products to the literal site labels. -/
theorem finite_fiber_density_domination (e : Fin (Fintype.card L) ≃ L)
    (s : ℕ) (hp : 0 < p) (hps : p ≤ s) (hn : ∀ i, FiberBlocks.size f i ≤ s)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (a x (f (e k))).val))-fiberProjector (p := p) f e ρ).PosSemidef := by
  obtain ⟨K,hK,nK,a,ha⟩ := finite_ambient_density_domination (FiberBlocks.size f) s hp hps hn ρ
    (FiberBlocks.total f) (FiberBlocks.regroup f e)
  let := hK
  let := nK
  refine ⟨K,hK,nK,a,?_⟩
  simpa only [groupedSite,FiberBlocks.label_regroup,fiberProjector] using ha

end CoordinateSweeps.SignedTensor
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
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Decomposition
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
lemma schattenMoment_unitary_left {d : ℕ} (q : ℕ) (A U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U.conjTranspose*U=1) : schattenMoment q (U*A)=schattenMoment q A := by
  unfold schattenMoment
  rw [Matrix.conjTranspose_mul]
  have hh : A.conjTranspose*U.conjTranspose*(U*A)=A.conjTranspose*A := by
    calc
      _ = A.conjTranspose*(U.conjTranspose*U)*A := by noncomm_ring
      _ = _ := by rw [hU,mul_one]
  rw [hh]

namespace Grid.Holes
variable {G : Grid} {h : ℕ} (H : G.Holes h)

lemma residualWithReference_eq (hf : H.Feasible)
    (ω0 ω : {ω : G.Choices // H.Compatible ω}) :
    H.residualWithReference ω0 ω=H.residualWithReference ω0 ⟨H.reference hf,H.reference_compatible hf⟩*
      H.residual hf ω := by
  apply Subtype.ext
  change (G.sweep ω0.val)⁻¹*G.sweep ω.val=
    ((G.sweep ω0.val)⁻¹*G.sweep (H.reference hf))*
      ((G.sweep (H.reference hf))⁻¹*G.sweep ω.val)
  group

theorem averageWithReference_moment (hf : H.Feasible)
    (ω0 : {ω : G.Choices // H.Compatible ω}) (z : ℝ) (ρ : UnitaryIrrep H.stabilizer) (q : ℕ) :
    schattenMoment q (H.averageWithReference ω0 z ρ)=schattenMoment q (H.conditionalAverage hf z ρ) := by
  have he : H.averageWithReference ω0 z ρ=
      ρ.matrix (H.residualWithReference ω0 ⟨H.reference hf,H.reference_compatible hf⟩)*
        H.conditionalAverage hf z ρ := by
    rw [H.conditionalAverage_eq_sum]
    unfold averageWithReference
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [H.residualWithReference_eq hf ω0 ω,map_mul,Matrix.mul_smul]
  rw [he]
  exact schattenMoment_unitary_left q _ _ (ρ.unitary _)

end Grid.Holes

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h : ℕ} (J : G.Holes h)

lemma outputStabilizer_residual (ω₀ ω : {ω : G.Choices // J.Compatible ω})
    (x : J.FreeAt (Fin.last G.b)) :
    (J.outputStabilizerEquiv ω₀ (J.residualWithReference ω₀ ω) x).val=
      G.sweep ω.val ((G.sweep ω₀.val)⁻¹ x.val) := by
  change G.sweep ω₀.val (((G.sweep ω₀.val)⁻¹*G.sweep ω.val) ((G.sweep ω₀.val)⁻¹ x.val))=_
  simp only [Equiv.Perm.mul_apply,Equiv.Perm.coe_inv,Equiv.apply_symm_apply]

variable {A B : Grid} (H : (concat A B).Holes h)

theorem rowResidual_fiber (hf : H.Feasible) (ω : H.RowChoices) (y : B.Slot)
    (x : {x : H.JunctionFree // H.rowLabel x=y}) :
    H.freeRow y ⟨H.junctionFreeEquiv (H.rowResidual hf ω) x.val,
      (H.rowResidual_label hf ω x.val).trans x.property⟩=
    (H.rowHoles y).outputStabilizerEquiv ((H.refPair hf).1 y)
      ((H.rowHoles y).residualWithReference ((H.refPair hf).1 y) (ω y)) (H.freeRow y x) := by
  apply Subtype.ext
  rw [outputStabilizer_residual]
  change (splitSlots A B ((H.rowResidual hf ω).val x.val.val)).1=_
  rw [H.rowResidual_split]
  change A.sweep (ω (H.rowLabel x.val)).val
    ((A.sweep ((H.refPair hf).1 (H.rowLabel x.val)).val)⁻¹ (splitSlots A B x.val.val).1)=_
  rw [x.property]
  rfl

/- Literal column-fiber permutation and the child's residual agree in its
input frame; this is where the row/column orientations differ. -/
theorem columnResidual_fiber (hf : H.Feasible) (ω : H.ColumnChoices) (y : A.Slot)
    (x : {x : H.JunctionFree // H.columnLabel x=y}) :
    H.freeColumn y ⟨H.junctionFreeEquiv (H.columnResidual hf ω) x.val,
      (H.columnResidual_label hf ω x.val).trans x.property⟩=
    (H.columnHoles y).stabilizerFreeEquiv
      ((H.columnHoles y).residualWithReference ((H.refPair hf).2 y) (ω y)) (H.freeColumn y x) := by
  apply Subtype.ext
  change (splitSlots A B ((H.columnResidual hf ω).val x.val.val)).2=_
  rw [H.columnResidual_split]
  change (B.sweep ((H.refPair hf).2 (H.columnLabel x.val)).val)⁻¹
    (B.sweep (ω (H.columnLabel x.val)).val (splitSlots A B x.val.val).2)=_
  rw [x.property]
  rfl
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

theorem row_restrict_eq (hf : H.Feasible) (ω : H.RowChoices) (i : Fin (Fintype.card B.Slot)) :
    restrict H.rowIndex (H.junctionFreeEquiv (H.rowResidual hf ω)) (H.rowResidual_index hf ω) i=
      H.rowChildEquiv hf i ((H.rowHoles (H.rowSite i)).residualWithReference
        ((H.refPair hf).1 (H.rowSite i)) (ω (H.rowSite i))) := by
  apply Equiv.ext
  intro j
  apply (H.rowLocalChart i).injective
  have hh := H.rowResidual_fiber hf ω (H.rowSite i)
    ⟨(cards H.rowIndex i j).val,(Fintype.equivFin B.Slot).eq_symm_apply.mpr (cards H.rowIndex i j).property⟩
  change H.rowLocalChart i (restrict H.rowIndex _ _ i j)=
    H.rowLocalChart i ((H.rowLocalChart i).symm
      ((H.rowHoles (H.rowSite i)).outputStabilizerEquiv ((H.refPair hf).1 (H.rowSite i))
        ((H.rowHoles (H.rowSite i)).residualWithReference ((H.refPair hf).1 (H.rowSite i)) (ω (H.rowSite i)))
        (H.rowLocalChart i j)))
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  have he := congrArg Subtype.val hh
  change (splitSlots A B (cards H.rowIndex i (restrict H.rowIndex _ _ i j)).val.val).1=_
  rw [restrict_apply]
  exact he

theorem column_restrict_eq (hf : H.Feasible) (ω : H.ColumnChoices) (i : Fin (Fintype.card A.Slot)) :
    restrict H.columnIndex (H.junctionFreeEquiv (H.columnResidual hf ω)) (H.columnResidual_index hf ω) i=
      H.columnChildEquiv i ((H.columnHoles (H.columnSite i)).residualWithReference
        ((H.refPair hf).2 (H.columnSite i)) (ω (H.columnSite i))) := by
  apply Equiv.ext
  intro j
  apply (H.columnLocalChart i).injective
  have hh := H.columnResidual_fiber hf ω (H.columnSite i)
    ⟨(cards H.columnIndex i j).val,(Fintype.equivFin A.Slot).eq_symm_apply.mpr (cards H.columnIndex i j).property⟩
  change H.columnLocalChart i (restrict H.columnIndex _ _ i j)=
    H.columnLocalChart i ((H.columnLocalChart i).symm
      ((H.columnHoles (H.columnSite i)).stabilizerFreeEquiv
        ((H.columnHoles (H.columnSite i)).residualWithReference ((H.refPair hf).2 (H.columnSite i)) (ω (H.columnSite i)))
        (H.columnLocalChart i j)))
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  have he := congrArg Subtype.val hh
  change (splitSlots A B (cards H.columnIndex i (restrict H.columnIndex _ _ i j)).val.val).2=_
  rw [restrict_apply]
  exact he

lemma rowResidual_as_fibers (hf : H.Feasible) (ω : H.RowChoices) :
    H.junctionFreeEquiv (H.rowResidual hf ω)=action H.rowIndex (fun i =>
      H.rowChildEquiv hf i ((H.rowHoles (H.rowSite i)).residualWithReference
        ((H.refPair hf).1 (H.rowSite i)) (ω (H.rowSite i)))) := by
  rw [← action_restrict H.rowIndex _ (H.rowResidual_index hf ω)]
  congr 1
  funext i
  exact H.row_restrict_eq hf ω i
lemma columnResidual_as_fibers (hf : H.Feasible) (ω : H.ColumnChoices) :
    H.junctionFreeEquiv (H.columnResidual hf ω)=action H.columnIndex (fun i =>
      H.columnChildEquiv i ((H.columnHoles (H.columnSite i)).residualWithReference
        ((H.refPair hf).2 (H.columnSite i)) (ω (H.columnSite i)))) := by
  rw [← action_restrict H.columnIndex _ (H.columnResidual_index hf ω)]
  congr 1
  funext i
  exact H.column_restrict_eq hf ω i
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks SignedTensor UnitaryIrrep
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

theorem rowAverage_eq_ambient (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) :
    H.rowAverage hf z (H.junctionTensorAction p e)=
      ambientAverage (p := p) (FiberBlocks.size H.rowIndex) (total H.rowIndex)
        (regroup H.rowIndex e) (H.rowLocalWeight z) (H.rowLocalPerm hf) := by
  unfold rowAverage ambientAverage averageMatrix
  apply Fintype.sum_equiv H.rowChoiceFinEquiv
  intro ω
  congr 1
  · rw [Complex.ofReal_prod]
    exact ((Fintype.equivFin B.Slot).symm.prod_comp
      (fun y => ((A.choiceWeight z (ω y).val/(H.rowHoles y).probability z : ℝ) : ℂ))).symm
  · change matrix (Equiv.permCongr e.symm (H.junctionFreeEquiv (H.rowResidual hf ω)))=_
    rw [H.rowResidual_as_fibers,ambient_action]
    rfl

theorem columnAverage_eq_ambient (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) :
    H.columnAverage hf z (H.junctionTensorAction p e)=
      ambientAverage (p := p) (FiberBlocks.size H.columnIndex) (total H.columnIndex)
        (regroup H.columnIndex e) (H.columnLocalWeight z) (H.columnLocalPerm hf) := by
  unfold columnAverage ambientAverage averageMatrix
  apply Fintype.sum_equiv H.columnChoiceFinEquiv
  intro ω
  congr 1
  · rw [Complex.ofReal_prod]
    exact ((Fintype.equivFin A.Slot).symm.prod_comp
      (fun x => ((B.choiceWeight z (ω x).val/(H.columnHoles x).probability z : ℝ) : ℂ))).symm
  · change matrix (Equiv.permCongr e.symm (H.junctionFreeEquiv (H.columnResidual hf ω)))=_
    rw [H.columnResidual_as_fibers,ambient_action]
    rfl

theorem rowLocalMoment (hf : H.Feasible) (z : ℝ) (q : ℕ) (i : Fin (Fintype.card B.Slot))
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i)))) :
    (Matrix.trace (((averageMatrix ρ.matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i)).conjTranspose*
      averageMatrix ρ.matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i))^q)).re=
      schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
        (H.rowHoles (H.rowSite i)).feasible_of_disjoint z (ρ.pullback (H.rowChildEquiv hf i))) := by
  exact (H.rowHoles (H.rowSite i)).averageWithReference_moment
    (H.rowHoles (H.rowSite i)).feasible_of_disjoint ((H.refPair hf).1 (H.rowSite i)) z (ρ.pullback (H.rowChildEquiv hf i)) q

theorem columnLocalMoment (hf : H.Feasible) (z : ℝ) (q : ℕ) (i : Fin (Fintype.card A.Slot))
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i)))) :
    (Matrix.trace (((averageMatrix ρ.matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i)).conjTranspose*
      averageMatrix ρ.matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i))^q)).re=
      schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
        (H.columnHoles (H.columnSite i)).feasible_of_disjoint z (ρ.pullback (H.columnChildEquiv i))) := by
  exact (H.columnHoles (H.columnSite i)).averageWithReference_moment
    (H.columnHoles (H.columnSite i)).feasible_of_disjoint ((H.refPair hf).2 (H.columnSite i)) z (ρ.pullback (H.columnChildEquiv i)) q

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
open scoped ComplexOrder
lemma evenTrace_real {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (q : ℕ) :
    Matrix.trace ((K.conjTranspose*K)^q)=((Matrix.trace ((K.conjTranspose*K)^q)).re : ℂ) := by
  have ht := ((Matrix.posSemidef_conjTranspose_mul_self K).pow q).trace_nonneg
  apply Complex.ext
  · rfl
  · simpa using ht.2.symm
end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks SignedTensor UnitaryIrrep
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

theorem row_projected_moment (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i)))) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.rowIndex) (total H.rowIndex) (regroup H.rowIndex e) ρ
    let X := H.rowAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((P*X).conjTranspose*(P*X))^q)).re=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (SignedTensor.action p (FiberBlocks.size H.rowIndex i)))) : ℝ)*
        schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
          (H.rowHoles (H.rowSite i)).feasible_of_disjoint z ((ρ i).pullback (H.rowChildEquiv hf i))) := by
  dsimp only
  rw [H.rowAverage_eq_ambient,ambient_projected_moment _ _ _ _ _ _ hq]
  have he (i : Fin (Fintype.card B.Slot)) :
      Matrix.trace (((averageMatrix (ρ i).matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i)).conjTranspose*
        averageMatrix (ρ i).matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i))^q)=
        (schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
          (H.rowHoles (H.rowSite i)).feasible_of_disjoint z ((ρ i).pullback (H.rowChildEquiv hf i))) : ℂ) := by
    rw [evenTrace_real,H.rowLocalMoment]
  simp only [he,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_prod,Complex.ofReal_re]

theorem column_projected_moment (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i)))) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.columnIndex) (total H.columnIndex) (regroup H.columnIndex e) ρ
    let Y := H.columnAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((P*Y).conjTranspose*(P*Y))^q)).re=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (SignedTensor.action p (FiberBlocks.size H.columnIndex i)))) : ℝ)*
        schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
          (H.columnHoles (H.columnSite i)).feasible_of_disjoint z ((ρ i).pullback (H.columnChildEquiv i))) := by
  dsimp only
  rw [H.columnAverage_eq_ambient,ambient_projected_moment _ _ _ _ _ _ hq]
  have he (i : Fin (Fintype.card A.Slot)) :
      Matrix.trace (((averageMatrix (ρ i).matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i)).conjTranspose*
        averageMatrix (ρ i).matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i))^q)=
        (schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
          (H.columnHoles (H.columnSite i)).feasible_of_disjoint z ((ρ i).pullback (H.columnChildEquiv i))) : ℂ) := by
    rw [evenTrace_real,H.columnLocalMoment]
  simp only [he,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_prod,Complex.ofReal_re]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks SignedTensor UnitaryIrrep
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
lemma row_size_le (i : Fin (Fintype.card B.Slot)) : FiberBlocks.size H.rowIndex i ≤ A.size := by
  have hc := Fintype.card_congr (H.rowLocalChart i)
  rw [Fintype.card_fin,(H.rowHoles (H.rowSite i)).card_freeAt] at hc
  rw [hc]
  exact Nat.sub_le _ _
lemma column_size_le (i : Fin (Fintype.card A.Slot)) : FiberBlocks.size H.columnIndex i ≤ B.size := by
  have hc := Fintype.card_congr (H.columnLocalChart i)
  rw [Fintype.card_fin,(H.columnHoles (H.columnSite i)).card_freeAt] at hc
  rw [hc]
  exact Nat.sub_le _ _

theorem row_moment_bound (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i))))
    (E : Fin (Fintype.card B.Slot) → ℝ)
    (hE : ∀ i, schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
      (H.rowHoles (H.rowSite i)).feasible_of_disjoint z ((ρ i).pullback (H.rowChildEquiv hf i))) ≤ Real.exp (E i)) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.rowIndex) (total H.rowIndex) (regroup H.rowIndex e) ρ
    let X := H.rowAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((P*X).conjTranspose*(P*X))^q)).re ≤
      ((A.size+1 : ℕ) : ℝ)^(B.size*((2*p)*(2*p)))*Real.exp (∑ i, E i) := by
  dsimp only
  rw [H.row_projected_moment p e hf z hq ρ]
  simpa only [card_slot] using child_product_bound (FiberBlocks.size H.rowIndex) A.size
    H.row_size_le ρ _ E (fun i => (H.rowHoles (H.rowSite i)).conditionalMoment_nonneg _ _ _ _) hE

theorem column_moment_bound (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i))))
    (E : Fin (Fintype.card A.Slot) → ℝ)
    (hE : ∀ i, schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
      (H.columnHoles (H.columnSite i)).feasible_of_disjoint z ((ρ i).pullback (H.columnChildEquiv i))) ≤ Real.exp (E i)) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.columnIndex) (total H.columnIndex) (regroup H.columnIndex e) ρ
    let Y := H.columnAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((Y*P).conjTranspose*(Y*P))^q)).re ≤
      ((B.size+1 : ℕ) : ℝ)^(A.size*((2*p)*(2*p)))*Real.exp (∑ i, E i) := by
  dsimp only
  have hc : _*_=_*_ := ambientProjector_commute_average (p := p) (FiberBlocks.size H.columnIndex)
    (total H.columnIndex) (regroup H.columnIndex e) ρ (H.columnLocalWeight z) (H.columnLocalPerm hf)
  rw [← H.columnAverage_eq_ambient] at hc
  rw [← hc,H.column_projected_moment p e hf z hq ρ]
  simpa only [card_slot] using child_product_bound (FiberBlocks.size H.columnIndex) B.size
    H.column_size_le ρ _ E (fun i => (H.columnHoles (H.columnSite i)).conditionalMoment_nonneg _ _ _ _) hE

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
-- module Solutions.OAIQ56_CS.Matrix_Holder
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
/- Required analytic interpolation for the matrix trace Hölder step06 (23).
A bounded holomorphic function on a tube over a box is bounded on the tube
over the convex hull of its bounded vertices. No Schatten assertion assumed. -/
noncomputable section
open Set Complex
open scoped BigOperators Topology
namespace CoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι]

lemma tubeUnitConvex {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    {M B : ℝ} (hB : ∀ z : ι → ℂ, inBox M (fun i => (z i).re) → ‖f z‖ ≤ B) :
    Convex ℝ {x : ι → ℝ | inBox M x ∧ tubeUnit f x} := by
  intro x hx y hy a b ha hb hab
  have habox : inBox M (a • x+b • y) := by
    intro i
    change 0 ≤ a*x i+b*y i ∧ a*x i+b*y i ≤ M
    constructor
    · exact add_nonneg (mul_nonneg ha (hx.1 i).1) (mul_nonneg hb (hy.1 i).1)
    · calc
        _ ≤ a*M+b*M := add_le_add
          (mul_le_mul_of_nonneg_left (hx.1 i).2 ha)
          (mul_le_mul_of_nonneg_left (hy.1 i).2 hb)
        _ = M := by rw [← add_mul,hab,one_mul]
  refine ⟨habox,?_⟩
  intro z hz
  let δ : ι → ℂ := fun i => ((y i-x i : ℝ) : ℂ)
  let g : ℂ → ℂ := fun w => f (z+(w-(b : ℂ)) • δ)
  have hgd : Differentiable ℂ g := by
    exact hf.comp (((differentiable_id.sub_const (b : ℂ)).smul_const δ).const_add z)
  have hre (w : ℂ) (i : ι) :
      (z i+(w-(b : ℂ))*δ i).re=(1-w.re)*x i+w.re*y i := by
    simp only [δ,add_re,mul_re,sub_re,ofReal_re,ofReal_im,mul_zero,sub_zero,hz]
    change a*x i+b*y i+(w.re-b)*(y i-x i)=_
    rw [show a=1-b by linarith]
    ring
  have hgB (w : ℂ) (hw : w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) : ‖g w‖ ≤ B := by
    apply hB
    intro i
    change 0 ≤ (z i+(w-(b : ℂ))*δ i).re ∧
      (z i+(w-(b : ℂ))*δ i).re ≤ M
    rw [hre]
    have hw0 : 0 ≤ w.re := hw.1
    have hw1 : w.re ≤ 1 := hw.2
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) (hx.1 i).1)
        (mul_nonneg hw0 (hy.1 i).1)
    · calc
        _ ≤ (1-w.re)*M+w.re*M := add_le_add
          (mul_le_mul_of_nonneg_left (hx.1 i).2 (by linarith))
          (mul_le_mul_of_nonneg_left (hy.1 i).2 hw0)
        _ = M := by ring
  have hl (w : ℂ) (hw : w.re=0) : ‖g w‖ ≤ 1 := by
    apply hx.2
    intro i
    change (z i+(w-(b : ℂ))*δ i).re=x i
    rw [hre,hw]; ring
  have hu (w : ℂ) (hw : w.re=1) : ‖g w‖ ≤ 1 := by
    apply hy.2
    intro i
    change (z i+(w-(b : ℂ))*δ i).re=y i
    rw [hre,hw]; ring
  have hbb : (b : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    exact ⟨hb,by simpa using show b ≤ 1 by linarith⟩
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := g) (z := (b : ℂ)) (a := (1 : ℝ)) (b := (1 : ℝ)) (l := 0) (u := 1)
    (by norm_num) hbb hgd.diffContOnCl (by
      exact ⟨B,fun w hw => by rcases hw with ⟨w,hw,rfl⟩; exact hgB w hw⟩)
    hl hu
  simpa [g] using h

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/- Equal-weight multivariate interpolation. At each vertex a single
coordinate has real part card ι; all imaginary parts remain unrestricted. -/
theorem tube_barycenter {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    {B : ℝ} (hB : ∀ z : ι → ℂ,
      inBox (Fintype.card ι) (fun i => (z i).re) → ‖f z‖ ≤ B)
    (hv : ∀ j, tubeUnit f (fun i => if i=j then Fintype.card ι else 0)) :
    tubeUnit f (fun _ => 1) := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hc := tubeUnitConvex hf hB
  have hw : ∑ _ : ι, N⁻¹=(1 : ℝ) := by simp [N,hN.ne']
  have hs := hc.sum_mem (t := Finset.univ) (w := fun _ : ι => N⁻¹)
    (z := fun j i => if i=j then (Fintype.card ι : ℝ) else 0)
    (fun _ _ => inv_nonneg.mpr hN.le) hw (by
      intro j hj
      refine ⟨?_,hv j⟩
      intro i
      dsimp only
      split_ifs
      · exact ⟨hN.le,le_rfl⟩
      · exact ⟨le_rfl,hN.le⟩)
  have he : (∑ j : ι, N⁻¹ • (fun i => if i=j then (Fintype.card ι : ℝ) else 0))=
      (fun _ : ι => (1 : ℝ)) := by
    funext i
    simp [Finset.sum_apply,Pi.smul_apply,N,hN.ne']
  rw [he] at hs
  exact hs.2

end CoordinateSweeps.TraceHolder

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma entry_norm_le (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let v : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have hv : ‖v‖=1 := by simp [v]
  have h := A.l2_opNorm_mulVec v
  have hi := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A.mulVec v)) i
  have he : ((EuclideanSpace.equiv n ℂ).symm (A.mulVec v)) i=A i j := by simp [v]
  rw [he] at hi
  rw [hv,mul_one] at h
  exact hi.trans h

lemma trace_norm_le (A : Matrix n n ℂ) :
    ‖Matrix.trace A‖ ≤ (Fintype.card n : ℝ)*‖A‖ := by
  calc
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : n, ‖A‖ := Finset.sum_le_sum (fun i _ => entry_norm_le A i i)
    _ = _ := by simp

lemma trace_diagonal_bound (d : n → ℂ) (B : Matrix n n ℂ) (hB : ‖B‖ ≤ 1) :
    ‖Matrix.trace (Matrix.diagonal d*B)‖ ≤ ∑ i, ‖d i‖ := by
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  calc
    _ ≤ ∑ i, ‖d i*B i i‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((entry_norm_le B i i).trans hB))

lemma list_prod_norm_le_one [Nonempty n] (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, ‖A‖ ≤ 1) :
    ‖L.prod‖ ≤ 1 := by
  induction L with
  | nil => simp
  | cons A L ih =>
    rw [List.prod_cons]
    have hA := hL A (by simp)
    have htail := ih (fun B hB => hL B (by simp [hB]))
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hA).trans htail)

lemma differentiable_matrix_list_prod_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : List (E → Matrix n n ℂ))
    (hL : ∀ f ∈ L, ∀ i j, Differentiable ℂ (fun z => f z i j)) :
    ∀ i j, Differentiable ℂ (fun z => (L.map (fun f => f z)).prod i j) := by
  induction L with
  | nil => intro i j; exact differentiable_const ((1 : Matrix n n ℂ) i j)
  | cons f L ih =>
    intro i j
    simp only [List.map_cons,List.prod_cons,Matrix.mul_apply]
    apply Differentiable.fun_sum
    intro k hk
    exact (hL f (by simp) i k).mul (ih (fun g hg => hL g (by simp [hg])) k j)

lemma positivePower_differentiable (x : ℝ) : Differentiable ℂ (positivePower x) := by
  unfold positivePower
  split_ifs
  · exact differentiable_const 0
  · fun_prop

lemma positivePower_one {x : ℝ} (hx : 0 ≤ x) : positivePower x 1=(x : ℂ) := by
  by_cases h : x=0
  · simp [positivePower,h]
  · simp [positivePower,h,← Complex.ofReal_exp,Real.exp_log (hx.lt_of_ne' h)]

lemma positivePower_norm_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖positivePower x z‖ ≤ 1 := by
  by_cases h : x=0
  · simp [positivePower,h]
  · rw [positivePower,ite_eq_right h,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hx hx1) hz)

lemma positivePower_norm_nat {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m)
    {z : ℂ} (hz : z.re=m) : ‖positivePower x z‖=x^m := by
  by_cases h : x=0
  · simp [positivePower,h,hm.ne']
  · rw [positivePower,ite_eq_right h,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hz]
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (hx.lt_of_ne' h)]

lemma norm_mul_diag_mul_le_one (U V : Matrix n n ℂ) (d : n → ℂ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1) :
    ‖U*Matrix.diagonal d*V‖ ≤ 1 := by
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hV
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) hU).trans
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hd

/- Ordered analytic product; factors may be noncommuting. -/

lemma differentiable_framed_diag_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U V : Matrix n n ℂ) (f : n → E → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (a b : n) :
    Differentiable ℂ (fun z => (U*Matrix.diagonal (fun i => f i z)*V) a b) := by
  have he (z : E) : (U*Matrix.diagonal (fun i => f i z)*V) a b=
      ∑ k, (U a k*f k z)*V k b := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  simp_rw [he]
  apply Differentiable.fun_sum
  intro k hk
  exact ((hf k).const_mul (U a k)).mul_const (V k b)

lemma traceFamily_differentiable {m : ℕ} (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ) :
    Differentiable ℂ (traceFamily U V dval) := by
  let F : Fin m → (Fin m → ℂ) → Matrix n n ℂ := fun j z =>
    U j*Matrix.diagonal (fun i => positivePower (dval j i) (z j))*V j
  have hF (j : Fin m) (a b : n) : Differentiable ℂ (fun z => F j z a b) := by
    apply differentiable_framed_diag_entries
    intro i
    exact (positivePower_differentiable (dval j i)).comp (differentiable_apply j)
  have hp := differentiable_matrix_list_prod_entries (List.ofFn F) (by
    intro f hf
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
    exact hF j)
  have ht : Differentiable ℂ (fun z => ∑ i, ((List.ofFn F).map (fun f => f z)).prod i i) := by
    apply Differentiable.fun_sum
    intro i hi
    exact hp i i
  have he : (fun z => ∑ i, ((List.ofFn F).map (fun f => f z)).prod i i)=
      traceFamily U V dval := by
    funext z
    simp only [traceFamily,F,List.map_ofFn,Matrix.trace,Matrix.diag,Function.comp_def]
  rw [he] at ht
  exact ht

lemma traceFamily_bound [Nonempty n] {m : ℕ} (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) (hdval : ∀ j i, 0 ≤ dval j i ∧ dval j i ≤ 1)
    (z : Fin m → ℂ) (hz : ∀ j, 0 ≤ (z j).re) :
    ‖traceFamily U V dval z‖ ≤ Fintype.card n := by
  apply (trace_norm_le _).trans
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  apply list_prod_norm_le_one
  intro A hA
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hA
  exact norm_mul_diag_mul_le_one (U j) (V j) _ (hU j) (hV j)
    (fun i => positivePower_norm_le (hdval j i).1 (hdval j i).2 (hz j))

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma single_diagonal_trace_bound {m : ℕ} (F : Fin m → Matrix n n ℂ) (j : Fin m)
    (U V : Matrix n n ℂ) (d : n → ℂ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hFj : F j=U*Matrix.diagonal d*V) (hF : ∀ k, k≠j → ‖F k‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn F).prod‖ ≤ ∑ i, ‖d i‖ := by
  let L := List.ofFn F
  have hj : j.val < L.length := by simp [L]
  have hnorm : ∀ l ∈ L.take j.val, ‖l‖ ≤ 1 := by
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_take_iff_getElem.mp hl
    have hkm : k < m := by simpa [L] using (lt_min_iff.mp hk).2
    change ‖(List.ofFn F)[k]‖ ≤ 1
    rw [List.getElem_ofFn]
    apply hF
    intro hh
    have he := congrArg Fin.val hh
    exact (Nat.ne_of_lt (lt_min_iff.mp hk).1) he
  have tnorm : ∀ l ∈ L.drop (j.val+1), ‖l‖ ≤ 1 := by
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_drop_iff_getElem.mp hl
    have hkm : j.val+1+k < m := by simpa [L,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hk
    change ‖(List.ofFn F)[j.val+1+k]'(by simpa using hkm)‖ ≤ 1
    rw [List.getElem_ofFn]
    apply hF
    intro hh
    have he := congrArg Fin.val hh
    dsimp only at he
    omega
  have hhead := list_prod_norm_le_one (L.take j.val) hnorm
  have htail := list_prod_norm_le_one (L.drop (j.val+1)) tnorm
  have he : L.prod=(L.take j.val).prod*(U*Matrix.diagonal d*V)*(L.drop (j.val+1)).prod := by
    rw [← List.prod_take_mul_prod_drop L j.val,List.drop_eq_getElem_cons hj,List.prod_cons]
    have hg : L[j.val]=F j := by simp [L]
    rw [hg,hFj]
    simp only [mul_assoc]
  change ‖Matrix.trace L.prod‖ ≤ _
  rw [he]
  have hcycle : Matrix.trace ((L.take j.val).prod*(U*Matrix.diagonal d*V)*
      (L.drop (j.val+1)).prod)=Matrix.trace (Matrix.diagonal d*
        (V*(L.drop (j.val+1)).prod*(L.take j.val).prod*U)) := by
    calc
      _ = Matrix.trace (((L.take j.val).prod*U)*
        (Matrix.diagonal d*(V*(L.drop (j.val+1)).prod))) := by simp only [mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_comm]; simp only [mul_assoc]
  rw [hcycle]
  apply trace_diagonal_bound
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hU
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hhead
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hV).trans htail)

lemma traceFamily_vertex {m : ℕ} (hm : 0 < m)
    (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) (hdval : ∀ j i, 0 ≤ dval j i ∧ dval j i ≤ 1)
    (hs : ∀ j, ∑ i, (dval j i)^m ≤ 1) (j : Fin m) :
    tubeUnit (traceFamily U V dval) (fun k => if k=j then m else 0) := by
  intro z hz
  have hzj : (z j).re=m := by simpa using hz j
  have hzk (k : Fin m) (hk : k≠j) : (z k).re=0 := by simpa [hk] using hz k
  apply (single_diagonal_trace_bound
    (fun k => U k*Matrix.diagonal (fun i => positivePower (dval k i) (z k))*V k) j
    (U j) (V j) (fun i => positivePower (dval j i) (z j)) (hU j) (hV j) rfl ?_).trans
  · simpa only [positivePower_norm_nat (hdval j _).1 hm hzj] using hs j
  · intro k hk
    exact norm_mul_diag_mul_le_one (U k) (V k) _ (hU k) (hV k)
      (fun i => positivePower_norm_le (hdval k i).1 (hdval k i).2 (by rw [hzk k hk]))

/- The complete normalized diagonal-factor trace Hölder estimate, for
arbitrarily many NONCOMMUTING factors. It is the analytic heart of06 eq23. -/
theorem diagonal_trace_holder {m : ℕ} (hm : 0 < m)
    (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) (hdval : ∀ j i, 0 ≤ dval j i ∧ dval j i ≤ 1)
    (hs : ∀ j, ∑ i, (dval j i)^m ≤ 1) :
    ‖Matrix.trace ((List.ofFn (fun j => U j*Matrix.diagonal
      (fun i => ((dval j i : ℝ) : ℂ))*V j)).prod)‖ ≤ 1 := by
  let : NeZero m := ⟨hm.ne'⟩
  have h := tube_barycenter (traceFamily_differentiable U V dval)
    (B := (Fintype.card n : ℝ))
    (fun z hz => traceFamily_bound U V dval hU hV hdval z (fun j => (hz j).1))
    (fun j => by simpa using traceFamily_vertex hm U V dval hU hV hdval hs j)
  have hh := h (fun _ => 1) (by simp)
  simpa [traceFamily,positivePower_one (hdval _ _).1] using hh

end CoordinateSweeps.TraceHolder

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma singular_nonneg (A : Matrix n n ℂ) (i : n) : 0 ≤ singular A i := Real.sqrt_nonneg _

lemma singular_sq (A : Matrix n n ℂ) (i : n) :
    singular A i^2=(gramHermitian A).eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

lemma rawPolar_gram (A : Matrix n n ℂ) :
    (rawPolar A).conjTranspose*rawPolar A=Matrix.diagonal
      (fun i => ((gramHermitian A).eigenvalues i : ℂ)) := by
  have h := (gramHermitian A).conjStarAlgAut_star_eigenvectorUnitary
  simpa only [rawPolar,rightBasis,Matrix.conjTranspose_mul,Unitary.conjStarAlgAut_star_apply,
    Matrix.star_eq_conjTranspose,mul_assoc,Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal] using h

omit [DecidableEq n] in
lemma zero_gram_column {B : Matrix n n ℂ} (j : n) (h : (B.conjTranspose*B) j j=0) :
    ∀ i, B i j=0 := by
  have hh := congrArg Complex.re h
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Complex.star_def,
    Complex.conj_mul',Complex.zero_re] at hh
  have hsum : ∑ i, ‖B i j‖^2=0 := by
    simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖B i j‖)).mp hsum
  intro i
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hzero i (Finset.mem_univ i)))

lemma rawPolar_zero_column (A : Matrix n n ℂ) (j : n) (hj : singular A j=0) :
    ∀ i, rawPolar A i j=0 := by
  apply zero_gram_column
  rw [rawPolar_gram,Matrix.diagonal_apply_eq,← singular_sq,hj]
  simp

lemma leftFrame_gram (A : Matrix n n ℂ) :
    (leftFrame A).conjTranspose*leftFrame A=
      Matrix.diagonal (fun i => if singular A i=0 then (0 : ℂ) else 1) := by
  simp only [leftFrame,Matrix.conjTranspose_mul,Matrix.diagonal_conjTranspose]
  rw [mul_assoc,← mul_assoc (rawPolar A).conjTranspose,rawPolar_gram,
    Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← singular_sq]
  by_cases hi : singular A i=0
  · simp [hi]
  · simp [hi,Complex.ofReal_inv,Complex.ofReal_pow]
    field_simp

lemma leftFrame_norm_le (A : Matrix n n ℂ) : ‖leftFrame A‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (leftFrame A)
  rw [leftFrame_gram,Matrix.l2_opNorm_diagonal] at hh
  have hb : ‖fun i => if singular A i=0 then (0 : ℂ) else 1‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    split_ifs <;> simp
  nlinarith [norm_nonneg (leftFrame A)]

lemma rightBasis_star_norm_le [Nonempty n] (A : Matrix n n ℂ) :
    ‖(rightBasis A : Matrix n n ℂ).conjTranspose‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (rightBasis A : Matrix n n ℂ)
  have hu := Unitary.coe_star_mul_self (rightBasis A)
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [hu,norm_one] at hh
  nlinarith [norm_nonneg (rightBasis A : Matrix n n ℂ)]

lemma polar_factors (A : Matrix n n ℂ) :
    leftFrame A*Matrix.diagonal (fun i => (singular A i : ℂ))*
      (rightBasis A : Matrix n n ℂ).conjTranspose=A := by
  have hh : leftFrame A*Matrix.diagonal (fun i => (singular A i : ℂ))=rawPolar A := by
    ext i j
    simp only [leftFrame,Matrix.mul_diagonal]
    by_cases hj : singular A j=0
    · simp [hj,rawPolar_zero_column A j hj i]
    · rw [mul_assoc]
      simp [hj]
  rw [hh,rawPolar,mul_assoc]
  have hu := Unitary.coe_mul_star_self (rightBasis A)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose] at hu
  rw [hu,mul_one]

lemma trace_moment_singular (A : Matrix n n ℂ) (q : ℕ) :
    (Matrix.trace ((A.conjTranspose*A)^q)).re=∑ i, singular A i^(2*q) := by
  have h := (gramHermitian A).spectral_theorem
  rw [h,← map_pow,Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self,one_mul,Matrix.diagonal_pow,Matrix.trace_diagonal]
  simp only [Complex.re_sum,Function.comp_def,Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_mul,singular_sq]
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma singularMass_nonneg (m : ℕ) (A : Matrix n n ℂ) : 0 ≤ singularMass m A :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (singular_nonneg A i) _)

lemma singularMass_eq_zero (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ)
    (h : singularMass m A=0) : A=0 := by
  have hs (i : n) : singular A i=0 := by
    have hi : singular A i^m ≤ singularMass m A :=
      Finset.single_le_sum (fun i _ => pow_nonneg (singular_nonneg A i) _) (Finset.mem_univ i)
    rw [h] at hi
    have hz : singular A i^m=0 := le_antisymm hi (pow_nonneg (singular_nonneg A i) _)
    exact (pow_eq_zero_iff hm.ne').mp hz
  have hf := polar_factors A
  simp only [hs,Complex.ofReal_zero,Matrix.diagonal_zero,mul_zero,zero_mul] at hf
  exact hf.symm

lemma schatten_nonneg (m : ℕ) (A : Matrix n n ℂ) : 0 ≤ schatten m A :=
  Real.rpow_nonneg (singularMass_nonneg m A) _

lemma schatten_pos (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) :
    0 < schatten m A := by
  apply Real.rpow_pos_of_pos
  exact lt_of_le_of_ne (singularMass_nonneg m A) (Ne.symm (fun hh => hA (singularMass_eq_zero m hm A hh)))

lemma schatten_pow (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) :
    schatten m A ^ m = singularMass m A :=
  Real.rpow_inv_natCast_pow (singularMass_nonneg m A) hm.ne'

lemma normalized_singular_sum (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) :
    ∑ i, (singular A i / schatten m A)^m = 1 := by
  simp_rw [div_pow]
  rw [← Finset.sum_div,schatten_pow m hm A]
  exact div_self (fun hh => hA (singularMass_eq_zero m hm A hh))

lemma normalized_singular_le (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) (i : n) :
    0 ≤ singular A i / schatten m A ∧ singular A i / schatten m A ≤ 1 := by
  have hpos := schatten_pos m hm A hA
  have hi : 0 ≤ singular A i / schatten m A := div_nonneg (singular_nonneg A i) hpos.le
  refine ⟨hi,?_⟩
  have hb : (singular A i / schatten m A)^m ≤ 1 := by
    rw [← normalized_singular_sum m hm A hA]
    exact Finset.single_le_sum (fun j _ => pow_nonneg (div_nonneg (singular_nonneg A j) hpos.le) _) (Finset.mem_univ i)
  by_contra hn
  have hgt : 1 < singular A i / schatten m A := lt_of_not_ge hn
  exact not_lt_of_ge hb (one_lt_pow₀ hgt hm.ne')

lemma normalized_polar (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) :
    (schatten m A : ℂ) • (leftFrame A * Matrix.diagonal
      (fun i => ((singular A i / schatten m A : ℝ) : ℂ)) * (rightBasis A : Matrix n n ℂ).conjTranspose) = A := by
  have hpos := schatten_pos m hm A hA
  have hc : (schatten m A : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [← Matrix.smul_mul,← Matrix.mul_smul]
  have hd : (schatten m A : ℂ) • Matrix.diagonal
      (fun i => ((singular A i / schatten m A : ℝ) : ℂ)) = Matrix.diagonal (fun i => (singular A i : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Complex.ofReal_div,hc,mul_div_cancel₀]
    · simp [hij]
  rw [hd,polar_factors]

lemma list_prod_scaled {m : ℕ} (c : Fin m → ℂ) (A : Fin m → Matrix n n ℂ) :
    (List.ofFn (fun j => c j • A j)).prod = (∏ j, c j) • (List.ofFn A).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ,List.prod_cons,Fin.prod_univ_succ,List.ofFn_succ,List.prod_cons,ih]
    exact smul_mul_smul_comm _ _ _ _

/- Genuine unnormalized Schatten trace Holder, built from the archived
complete interpolation and polar-frame proofs rather than assumed. -/
theorem matrix_trace_holder [Nonempty n] {m : ℕ} (hm : 0 < m) (A : Fin m → Matrix n n ℂ) :
    ‖Matrix.trace (List.ofFn A).prod‖ ≤ ∏ j, schatten m (A j) := by
  by_cases hA : ∀ j, A j ≠ 0
  · let d := fun j i => singular (A j) i / schatten m (A j)
    let B := fun j => leftFrame (A j) * Matrix.diagonal (fun i => (d j i : ℂ)) *
      (rightBasis (A j) : Matrix n n ℂ).conjTranspose
    have hb : ‖Matrix.trace (List.ofFn B).prod‖ ≤ 1 :=
      diagonal_trace_holder hm (fun j => leftFrame (A j))
        (fun j => (rightBasis (A j) : Matrix n n ℂ).conjTranspose) d
        (fun j => leftFrame_norm_le _) (fun j => rightBasis_star_norm_le _)
        (fun j i => normalized_singular_le m hm (A j) (hA j) i)
        (fun j => (normalized_singular_sum m hm (A j) (hA j)).le)
    have he : A = fun j => (schatten m (A j) : ℂ) • B j := by
      funext j
      exact (normalized_polar m hm (A j) (hA j)).symm
    conv_lhs => rw [he,list_prod_scaled,Matrix.trace_smul,norm_smul]
    have hc : ‖∏ j, (schatten m (A j) : ℂ)‖ = ∏ j, schatten m (A j) := by
      rw [norm_prod]
      apply Finset.prod_congr rfl
      intro j _
      simp [Complex.norm_real,abs_of_nonneg (schatten_nonneg m (A j))]
    rw [hc]
    exact mul_le_of_le_one_right (Finset.prod_nonneg (fun j _ => schatten_nonneg m _)) hb
  · push Not at hA
    obtain ⟨j,hj⟩ := hA
    have hz : (List.ofFn A).prod = 0 := List.prod_eq_zero (List.mem_ofFn.mpr ⟨j,hj⟩)
    rw [hz,Matrix.trace_zero,norm_zero]
    exact Finset.prod_nonneg (fun j _ => schatten_nonneg m _)

lemma schatten_even_eq (q : ℕ) (A : Matrix n n ℂ) :
    schatten (2*q) A = (Matrix.trace ((A.conjTranspose*A)^q)).re ^ ((2*q : ℝ)⁻¹) := by
  rw [trace_moment_singular]
  simp only [schatten,singularMass,Nat.cast_mul,Nat.cast_ofNat]

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]
open scoped ComplexOrder

lemma trace_mul_pow_comm (A B : Matrix n n ℂ) (q : ℕ) :
    Matrix.trace ((A*B)^q) = Matrix.trace ((B*A)^q) := by
  cases q with
  | zero => rfl
  | succ q =>
    rw [pow_succ,← mul_assoc,mul_pow_mul,Matrix.trace_mul_cycle,← pow_succ']

lemma schatten_adjoint_even (q : ℕ) (A : Matrix n n ℂ) :
    schatten (2*q) A.conjTranspose = schatten (2*q) A := by
  simp only [schatten_even_eq,Matrix.conjTranspose_conjTranspose]
  rw [trace_mul_pow_comm]

lemma trace_moment_norm (q : ℕ) (A : Matrix n n ℂ) :
    ‖Matrix.trace ((A.conjTranspose*A)^q)‖ = singularMass (2*q) A := by
  have ht := ((Matrix.posSemidef_conjTranspose_mul_self A).pow q).trace_nonneg
  rw [← show (Matrix.trace ((A.conjTranspose*A)^q)).re = singularMass (2*q) A from
    trace_moment_singular A q]
  have him : (Matrix.trace ((A.conjTranspose*A)^q)).im=0 := by simpa using ht.2.symm
  have hre : 0 ≤ (Matrix.trace ((A.conjTranspose*A)^q)).re := by simpa using ht.1
  have he : Matrix.trace ((A.conjTranspose*A)^q) =
      ((Matrix.trace ((A.conjTranspose*A)^q)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  conv_lhs => rw [he]
  simp [Complex.norm_real,abs_of_nonneg hre]

lemma schatten_even_pow (q : ℕ) (hq : 0 < q) (A : Matrix n n ℂ) :
    schatten (2*q) A ^ (2*q) = (Matrix.trace ((A.conjTranspose*A)^q)).re := by
  rw [schatten_pow _ (by omega)]
  exact (trace_moment_singular A q).symm

lemma schatten_zero_even (q : ℕ) (hq : 0 < q) :
    schatten (2*q) (0 : Matrix n n ℂ)=0 := by
  apply (pow_eq_zero_iff (show 2*q ≠ 0 by omega)).mp
  rw [schatten_even_pow q hq]
  simp [hq.ne']

lemma matrix_trace_holder_list [Nonempty n] (L : List (Matrix n n ℂ)) (hL : 0 < L.length) :
    ‖Matrix.trace L.prod‖ ≤ (L.map (schatten L.length)).prod := by
  have hh := matrix_trace_holder hL L.get
  rw [← List.prod_ofFn] at hh
  simpa only [List.ofFn_comp', List.ofFn_get] using hh

/- Odd alternating word completing one Gram trace to an even moment. -/

omit [Fintype n] [DecidableEq n] in
lemma oddWord_length (q : ℕ) (A : Matrix n n ℂ) :
    (oddWord q A).length = 2*q+1 := by
  simp [oddWord,List.length_flatten]
  omega

lemma oddWord_prod (q : ℕ) (A : Matrix n n ℂ) :
    (oddWord q A).prod=A*(A.conjTranspose*A)^q := by
  simp [oddWord,List.prod_flatten]

lemma oddWord_schatten_prod (q : ℕ) (A : Matrix n n ℂ) :
    ((oddWord q A).map (schatten (2*(q+1)))).prod =
      schatten (2*(q+1)) A ^ (2*q+1) := by
  simp only [oddWord,List.map_cons,List.map_flatten,List.map_replicate,List.map_nil,
    List.prod_cons,List.prod_nil,List.prod_flatten,List.prod_replicate,
    schatten_adjoint_even,mul_one]
  ring

/- The literal unnormalized even Schatten triangle inequality, for a finite
sum, derived from genuine matrix trace Holder rather than postulated. -/
theorem schatten_even_sum_le [Nonempty n] {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q)
    (A : I → Matrix n n ℂ) :
    schatten (2*q) (∑ i, A i) ≤ ∑ i, schatten (2*q) (A i) := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  let B := ∑ i, A i
  let t := schatten (2*(r+1)) B
  by_cases hB : B=0
  · change schatten (2*(r+1)) B ≤ _
    rw [hB,schatten_zero_even (r+1) (by omega)]
    exact Finset.sum_nonneg fun i _ => schatten_nonneg _ _
  · have ht : 0 < t := schatten_pos _ (by omega) B hB
    have hc (i : I) :
        ‖Matrix.trace ((A i).conjTranspose * (oddWord r B).prod)‖ ≤
          schatten (2*(r+1)) (A i) * t^(2*r+1) := by
      have hh := matrix_trace_holder_list ((A i).conjTranspose :: oddWord r B) (by simp)
      simpa only [List.length_cons,oddWord_length,show 2*r+1+1=2*(r+1) by omega,
        List.prod_cons,List.map_cons,schatten_adjoint_even,oddWord_schatten_prod] using hh
    have he : Matrix.trace ((B.conjTranspose*B)^(r+1)) =
        ∑ i, Matrix.trace ((A i).conjTranspose*(oddWord r B).prod) := by
      rw [pow_succ',mul_assoc,oddWord_prod]
      change Matrix.trace (((∑ i, A i).conjTranspose)*(B*(B.conjTranspose*B)^r)) = _
      rw [Matrix.conjTranspose_sum,Finset.sum_mul,Matrix.trace_sum]
    have hh : t^(2*(r+1)) ≤ (∑ i, schatten (2*(r+1)) (A i)) * t^(2*r+1) := by
      calc
        _ = ‖Matrix.trace ((B.conjTranspose*B)^(r+1))‖ := by
          change schatten (2*(r+1)) B ^ (2*(r+1)) = _
          rw [trace_moment_norm,schatten_pow _ (by omega)]
        _ ≤ ∑ i, ‖Matrix.trace ((A i).conjTranspose*(oddWord r B).prod)‖ := by
          rw [he]; exact norm_sum_le _ _
        _ ≤ ∑ i, schatten (2*(r+1)) (A i) * t^(2*r+1) := Finset.sum_le_sum (fun i _ => hc i)
        _ = _ := (Finset.sum_mul ..).symm
    have hh' : t * t^(2*r+1) ≤ (∑ i, schatten (2*(r+1)) (A i))*t^(2*r+1) := by
      calc
        _ = t^(2*(r+1)) := by
          rw [show 2*(r+1)=(2*r+1)+1 by omega]
          simp only [pow_succ]
          ring
        _ ≤ _ := hh
    change t ≤ ∑ i, schatten (2*(r+1)) (A i)
    exact (mul_le_mul_iff_left₀ (pow_pos ht (2*r+1))).mp hh'

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma matrix_trace_holder_contractions {m : ℕ} (hm : 0 < m)
    (A C : Fin m → Matrix n n ℂ) (hC : ∀ j, ‖C j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => A j*C j)).prod‖ ≤ ∏ j, schatten m (A j) := by
  by_cases hA : ∀ j, A j ≠ 0
  · let d := fun j i => singular (A j) i / schatten m (A j)
    let V := fun j => (rightBasis (A j) : Matrix n n ℂ).conjTranspose*C j
    let B := fun j => leftFrame (A j) * Matrix.diagonal (fun i => (d j i : ℂ)) * V j
    have hv (j) : ‖V j‖ ≤ 1 := (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (rightBasis_star_norm_le _)).trans (hC j))
    have hb : ‖Matrix.trace (List.ofFn B).prod‖ ≤ 1 :=
      diagonal_trace_holder hm (fun j => leftFrame (A j)) V d
        (fun j => leftFrame_norm_le _) hv
        (fun j i => normalized_singular_le m hm (A j) (hA j) i)
        (fun j => (normalized_singular_sum m hm (A j) (hA j)).le)
    have he : (fun j => A j*C j) = fun j => (schatten m (A j) : ℂ) • B j := by
      funext j
      have hh := congrArg (fun M : Matrix n n ℂ => M*C j) (normalized_polar m hm (A j) (hA j))
      simpa only [B,V,d,Matrix.smul_mul,mul_assoc] using hh.symm
    rw [he,list_prod_scaled,Matrix.trace_smul,norm_smul,norm_prod]
    have hc : (∏ j, ‖(schatten m (A j) : ℂ)‖) = ∏ j, schatten m (A j) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [Complex.norm_real,abs_of_nonneg (schatten_nonneg m (A j))]
    rw [hc]
    exact mul_le_of_le_one_right (Finset.prod_nonneg (fun j _ => schatten_nonneg m _)) hb
  · push Not at hA
    obtain ⟨j,hj⟩ := hA
    have hz : (List.ofFn (fun j => A j*C j)).prod=0 := by
      apply List.prod_eq_zero
      exact List.mem_ofFn.mpr ⟨j,by simp [hj]⟩
    rw [hz,Matrix.trace_zero,norm_zero]
    exact Finset.prod_nonneg (fun j _ => schatten_nonneg m _)

lemma matrix_trace_holder_mixed {m : ℕ} (hm : 0 < m) (A C : Fin m → Matrix n n ℂ) :
    ‖Matrix.trace (List.ofFn (fun j => A j*C j)).prod‖ ≤
      ∏ j, schatten m (A j)*‖C j‖ := by
  by_cases hC : ∀ j, C j ≠ 0
  · let C' := fun j => (‖C j‖⁻¹ : ℂ) • C j
    have hc (j) : ‖C' j‖ ≤ 1 := by
      have hp := norm_pos_iff.mpr (hC j)
      simp [C',norm_smul,Complex.norm_real,hp.ne']
    have hb := matrix_trace_holder_contractions hm A C' hc
    have he : (fun j => A j*C j) = fun j => (‖C j‖ : ℂ) • (A j*C' j) := by
      funext j
      have hp : (‖C j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hC j)
      have hc' : (‖C j‖ : ℂ) • C' j = C j := by
        ext a b
        simp [C',Matrix.smul_apply,smul_eq_mul,hp]
      rw [← Matrix.mul_smul,hc']
    rw [he,list_prod_scaled,Matrix.trace_smul,norm_smul,norm_prod]
    have hn : (∏ j, ‖(‖C j‖ : ℂ)‖) = ∏ j, ‖C j‖ := by simp
    rw [hn,Finset.prod_mul_distrib]
    exact (mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun j _ => norm_nonneg _))).trans_eq (mul_comm _ _)
  · push Not at hC
    obtain ⟨j,hj⟩ := hC
    have hz : (List.ofFn (fun j => A j*C j)).prod=0 := by
      apply List.prod_eq_zero
      exact List.mem_ofFn.mpr ⟨j,by simp [hj]⟩
    rw [hz,Matrix.trace_zero,norm_zero]
    exact Finset.prod_nonneg fun j _ => mul_nonneg (schatten_nonneg m _) (norm_nonneg _)

lemma matrix_trace_holder_mixed_list (L : List (Matrix n n ℂ × Matrix n n ℂ))
    (hL : 0 < L.length) :
    ‖Matrix.trace (L.map (fun d => d.1*d.2)).prod‖ ≤
      (L.map (fun d => schatten L.length d.1*‖d.2‖)).prod := by
  have hh := matrix_trace_holder_mixed hL (fun j => (L.get j).1) (fun j => (L.get j).2)
  rw [← List.prod_ofFn] at hh
  have h₁ : List.ofFn (fun j => (L.get j).1*(L.get j).2) = L.map (fun d => d.1*d.2) := by
    simpa only [List.ofFn_get] using List.ofFn_comp' L.get (fun d => d.1*d.2)
  have h₂ : List.ofFn (fun j => schatten L.length (L.get j).1*‖(L.get j).2‖) =
      L.map (fun d => schatten L.length d.1*‖d.2‖) := by
    simpa only [List.ofFn_get] using List.ofFn_comp' L.get (fun d => schatten L.length d.1*‖d.2‖)
  rwa [h₁,h₂] at hh

/- Right ideal inequality for the exact even Schatten norm. -/
theorem schatten_even_mul_right (q : ℕ) (hq : 0 < q) (A C : Matrix n n ℂ) :
    schatten (2*q) (A*C) ≤ schatten (2*q) A * ‖C‖ := by
  let L : List (Matrix n n ℂ × Matrix n n ℂ) :=
    (List.replicate q [(A.conjTranspose,1),(A,C*C.conjTranspose)]).flatten
  have hl : L.length=2*q := by simp [L,List.length_flatten]; omega
  have hh := matrix_trace_holder_mixed_list L (by rw [hl]; omega)
  have hp : (L.map (fun d => d.1*d.2)).prod = (A.conjTranspose*A*(C*C.conjTranspose))^q := by
    simp [L,List.map_flatten,List.prod_flatten,mul_assoc]
  have ht' : Matrix.trace (((A*C).conjTranspose*(A*C))^q) =
      Matrix.trace ((A.conjTranspose*A*(C*C.conjTranspose))^q) := by
    rw [Matrix.conjTranspose_mul]
    have he : C.conjTranspose*A.conjTranspose*(A*C)=C.conjTranspose*(A.conjTranspose*A*C) := by simp only [mul_assoc]
    rw [he,trace_mul_pow_comm]
    simp only [mul_assoc]
  have hn : ‖C*C.conjTranspose‖=‖C‖^2 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self C.conjTranspose
    simpa only [Matrix.conjTranspose_conjTranspose,Matrix.l2_opNorm_conjTranspose,pow_two] using h
  have hr : (L.map (fun d => schatten L.length d.1 * ‖d.2‖)).prod =
      (schatten (2*q) A*‖C‖)^(2*q) := by
    rw [hl]
    simp only [L,List.map_flatten,List.map_replicate,List.map_cons,List.map_nil,
      List.prod_flatten,List.prod_replicate,List.prod_cons,List.prod_nil,
      schatten_adjoint_even,norm_one,mul_one,hn]
    rw [pow_mul]
    congr 1
    ring
  rw [hp,← ht',trace_moment_norm,hr,← schatten_pow _ (by omega)] at hh
  exact (pow_le_pow_iff_left₀ (schatten_nonneg _ _) (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _)) (by omega)).mp hh

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma norm_le_schatten (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) :
    ‖A‖ ≤ schatten m A := by
  by_cases hA : A=0
  · rw [hA,norm_zero]
    exact schatten_nonneg _ _
  · let d := fun i => singular A i / schatten m A
    let B := leftFrame A*Matrix.diagonal (fun i => (d i : ℂ))*(rightBasis A : Matrix n n ℂ).conjTranspose
    have hb : ‖B‖ ≤ 1 := norm_mul_diag_mul_le_one _ _ _ (leftFrame_norm_le A)
      (rightBasis_star_norm_le A) (fun i => by
        simpa only [d,Complex.norm_real,Real.norm_of_nonneg (normalized_singular_le m hm A hA i).1] using
          (normalized_singular_le m hm A hA i).2)
    have he : A=(schatten m A : ℂ) • B := (normalized_polar m hm A hA).symm
    calc
      ‖A‖ = schatten m A * ‖B‖ := by
        conv_lhs => rw [he,norm_smul]
        rw [Complex.norm_real,Real.norm_of_nonneg (schatten_nonneg _ _)]
      _ ≤ schatten m A := mul_le_of_le_one_right (schatten_nonneg m A) hb

lemma schatten_even_mul_left (q : ℕ) (hq : 0 < q) (A C : Matrix n n ℂ) :
    schatten (2*q) (A*C) ≤ ‖A‖ * schatten (2*q) C := by
  have hh := schatten_even_mul_right q hq C.conjTranspose A.conjTranspose
  rw [← Matrix.conjTranspose_mul,schatten_adjoint_even,schatten_adjoint_even,
    Matrix.l2_opNorm_conjTranspose] at hh
  exact hh.trans_eq (mul_comm _ _)

/- The exact three factor inequality used by06:eq20. -/
theorem schatten_even_three (q : ℕ) (hq : 0 < q) (A B C : Matrix n n ℂ) :
    schatten (2*q) (A*B*C) ≤ schatten (2*q) A * ‖B‖ * schatten (2*q) C := by
  calc
    _ ≤ schatten (2*q) (A*B)*‖C‖ := schatten_even_mul_right q hq _ _
    _ ≤ (schatten (2*q) A*‖B‖)*schatten (2*q) C :=
      mul_le_mul (schatten_even_mul_right q hq _ _) (norm_le_schatten _ (by omega) C)
        (norm_nonneg _) (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _))

lemma schatten_even_smul_le (q : ℕ) (hq : 0 < q) (c : ℂ) (A : Matrix n n ℂ) :
    schatten (2*q) (c • A) ≤ ‖c‖ * schatten (2*q) A := by
  have hh := schatten_even_mul_left q hq (c • (1 : Matrix n n ℂ)) A
  simpa only [Matrix.smul_mul,one_mul,norm_smul,norm_one,mul_one] using hh

end CoordinateSweeps.TraceHolder
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
lemma projector_norm_le (P : Matrix n n ℂ) (hP : P.IsHermitian) (hP2 : P*P=P) :
    ‖P‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP.eq,hP2] at hh
  nlinarith [norm_nonneg P]

/- Exact resolution-of-two-subgroups inequality used in source06:eq20. No
orthogonality or occurrence is silently supplied: identity and idempotence
are explicit algebraic premises discharged by the genuine type resolution. -/
theorem row_column_schatten {I J : Type*} [Fintype I] [Fintype J]
    (q : ℕ) (hq : 0 < q) (PR : I → Matrix n n ℂ) (PC : J → Matrix n n ℂ)
    (hR : ∑ i, PR i=1) (hC : ∑ j, PC j=1)
    (hR2 : ∀ i, PR i*PR i=PR i) (hC2 : ∀ j, PC j*PC j=PC j)
    (P X Y : Matrix n n ℂ) :
    schatten (2*q) (Y*P*X) ≤
      ∑ ij : J × I, schatten (2*q) (Y*PC ij.1)*
        ‖PC ij.1*P*PR ij.2‖*schatten (2*q) (PR ij.2*X) := by
  have he : (∑ ij : J × I, (Y*PC ij.1)*(PC ij.1*P*PR ij.2)*(PR ij.2*X))=Y*P*X := by
    simp only [Fintype.sum_prod_type]
    have hterm (j : J) (i : I) :
        (Y*PC j)*(PC j*P*PR i)*(PR i*X)=Y*PC j*P*PR i*X := by
      calc
        _ = Y*(PC j*PC j)*P*(PR i*PR i)*X := by simp only [mul_assoc]
        _ = _ := by rw [hC2,hR2]
    simp only [hterm]
    simp only [← Matrix.sum_mul,← Matrix.mul_sum,hR,hC,mul_one]
  calc
    _ = schatten (2*q) (∑ ij : J × I, (Y*PC ij.1)*(PC ij.1*P*PR ij.2)*(PR ij.2*X)) := by rw [he]
    _ ≤ ∑ ij : J × I, schatten (2*q) ((Y*PC ij.1)*(PC ij.1*P*PR ij.2)*(PR ij.2*X)) :=
      schatten_even_sum_le q hq _
    _ ≤ _ := Finset.sum_le_sum (fun ij _ => schatten_even_three q hq _ _ _)

lemma contraction_power_from_overlap {t B c : ℝ} (q : ℕ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hc : 0 ≤ c) (hcq : c ≤ q)
    (hB : t^2 ≤ Real.exp B) :
    t^(2*q) ≤ Real.exp (c*B) := by
  calc
    _ = (t^2)^q := pow_mul t 2 q
    _ = (t^2)^(q : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (t^2)^c := Real.rpow_le_rpow_of_exponent_ge' (sq_nonneg t)
      (pow_le_one₀ ht ht1) hc hcq
    _ ≤ (Real.exp B)^c := Real.rpow_le_rpow (sq_nonneg t) hB hc
    _ = _ := by rw [← Real.exp_mul]; congr 1; ring

/- Algebraic cancellation of subgroup dimensions, preserving the absolute
(not normalized) even moment. This is the quantitative core of06:eq21. -/
theorem row_column_moment {I J : Type*} [Fintype I] [Fintype J]
    (q : ℕ) (hq : 0 < q) (PR : I → Matrix n n ℂ) (PC : J → Matrix n n ℂ)
    (hR : ∑ i, PR i=1) (hC : ∑ j, PC j=1)
    (hR2 : ∀ i, PR i*PR i=PR i) (hC2 : ∀ j, PC j*PC j=PC j)
    (P X Y : Matrix n n ℂ) (FR : I → ℝ) (FC : J → ℝ) (F A B c : ℝ)
    (hc : 0 ≤ c) (hcq : c ≤ q)
    (hchild : ∀ i j,
      (Matrix.trace (((PR i*X).conjTranspose*(PR i*X))^q)).re *
        (Matrix.trace (((Y*PC j).conjTranspose*(Y*PC j))^q)).re ≤
          Real.exp (-c*(FR i+FC j)+A))
    (hoverlap : ∀ i j, ‖PC j*P*PR i‖^2 ≤ Real.exp (FR i+FC j-F+B))
    (hcontract : ∀ i j, ‖PC j*P*PR i‖ ≤ 1) :
    (Matrix.trace (((Y*P*X).conjTranspose*(Y*P*X))^q)).re ≤
      ((Fintype.card I*Fintype.card J : ℕ) : ℝ)^(2*q)*Real.exp (-c*F+A+c*B) := by
  let E := Real.exp ((-c*F+A+c*B)/(2*q : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hEq : E^(2*q)=Real.exp (-c*F+A+c*B) := by
    dsimp [E]
    rw [← Real.exp_nat_mul]
    congr 1
    have hq0 : (2*q : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hb (j : J) (i : I) :
      schatten (2*q) (Y*PC j)*‖PC j*P*PR i‖*schatten (2*q) (PR i*X) ≤ E := by
    apply (pow_le_pow_iff_left₀ (mul_nonneg (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _)) (schatten_nonneg _ _)) hE (show 2*q ≠ 0 by omega)).mp
    rw [hEq]
    simp only [mul_pow,schatten_even_pow q hq]
    have hch := hchild i j
    have hp := contraction_power_from_overlap q (norm_nonneg _) (hcontract i j) hc hcq (hoverlap i j)
    calc
      _ = ((Matrix.trace (((PR i*X).conjTranspose*(PR i*X))^q)).re *
            (Matrix.trace (((Y*PC j).conjTranspose*(Y*PC j))^q)).re) *
                ‖PC j*P*PR i‖^(2*q) := by ring
      _ ≤ Real.exp (-c*(FR i+FC j)+A)*Real.exp (c*(FR i+FC j-F+B)) :=
        mul_le_mul hch hp (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs : schatten (2*q) (Y*P*X) ≤ (Fintype.card I*Fintype.card J : ℕ)*E := by
    apply (row_column_schatten q hq PR PC hR hC hR2 hC2 P X Y).trans
    calc
      _ ≤ ∑ _ : J × I, E := Finset.sum_le_sum (fun ij _ => hb ij.1 ij.2)
      _ = _ := by simp [Fintype.card_prod,Nat.mul_comm]
  have hp := pow_le_pow_left₀ (schatten_nonneg _ _) hs (2*q)
  rw [schatten_even_pow q hq,mul_pow,hEq] at hp
  exact hp

end CoordinateSweeps.TraceHolder

end
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
-- module Solutions.OAIQ56_CS.Unitary_Spectral
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

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma projector_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) :
    Matrix.trace (ρ.projector τ) = (ρ.dimension : ℂ) *
      Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
  simp only [projector,Matrix.trace_sum,Matrix.trace_smul,coefficient,smul_eq_mul]
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        ∑ g, Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by
      rw [ρ.character_sum_multiplicity τ]
      have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

lemma dimension_le_of_projector_one (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    [Nonempty n] (h : ρ.projector τ = 1) : ρ.dimension ≤ Fintype.card n := by
  have he := ρ.projector_trace τ
  rw [h,Matrix.trace_one] at he
  have he' : Fintype.card n = ρ.dimension *
    Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by exact_mod_cast he
  have hm : 0 < Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
    have hn := Fintype.card_pos (α := n)
    by_contra hh
    have hz := Nat.eq_zero_of_not_pos hh
    rw [hz,mul_zero] at he'
    omega
  rw [he']
  exact Nat.le_mul_of_pos_right _ hm

lemma projector_map (ρ : UnitaryIrrep Γ) {m : Type*} [Fintype m] [DecidableEq m]
    (e : Matrix n n ℂ →ₐ[ℂ] Matrix m m ℂ) (τ : Γ →* Matrix n n ℂ) :
    ρ.projector (e.toMonoidHom.comp τ) = e (ρ.projector τ) := by
  change (∑ g, ρ.coefficient g • e (τ g)) = e (∑ g, ρ.coefficient g • τ g)
  simp only [map_sum,map_smul]

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.SpectralBlock
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma projector_representation (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (r : n → ℝ) (v : ℝ) (hτ : ∀ g i j, r i ≠ r j → τ g i j=0) :
    ρ.projector (representation τ r v hτ) =
      (ρ.projector τ).submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) := by
  ext i j
  simp [UnitaryIrrep.projector,Matrix.sum_apply,representation]

omit [Fintype Γ] in
lemma offDiagonal_zero (τ : Γ →* Matrix n n ℂ) (r : n → ℝ)
    (hτ : ∀ g, τ g * Matrix.diagonal (fun i => (r i : ℂ)) =
      Matrix.diagonal (fun i => (r i : ℂ)) * τ g) :
    ∀ g i j, r i ≠ r j → τ g i j=0 := by
  intro g i j hij
  have he := congrArg (fun M : Matrix n n ℂ => M i j) (hτ g)
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] at he
  by_contra hn
  apply hij
  exact Complex.ofReal_injective (mul_left_cancel₀ hn (he.trans (mul_comm _ _))).symm

lemma projector_on_level (P : Matrix n n ℂ) (r : n → ℝ) (v : ℝ) (hv : v ≠ 0)
    (hP : P * Matrix.diagonal (fun i => (r i : ℂ)) = Matrix.diagonal (fun i => (r i : ℂ))) :
    P.submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) = 1 := by
  ext i j
  have he := congrArg (fun M : Matrix n n ℂ => M i.val j.val) hP
  simp only [Matrix.mul_diagonal,Matrix.diagonal_apply] at he
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  apply mul_right_cancel₀ hv'
  change P i.val j.val * (v : ℂ) = (1 : Matrix (Level r v) (Level r v) ℂ) i j * (v : ℂ)
  simpa only [i.property,j.property,Matrix.one_apply,Subtype.val_inj,ite_mul,one_mul,zero_mul] using he

omit [DecidableEq n] in
lemma level_card_le_trace (r : n → ℝ) (hr : ∀ i, 0 ≤ r i) (v : ℝ) :
    Fintype.card (Level r v) * v ≤ ∑ i, r i := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => r i=v)]
  have he : ∑ i : Level r v, r i.val = Fintype.card (Level r v) * v := by
    simp_rw [show ∀ i : Level r v, r i.val = v from fun i => i.property]
    simp
  rw [he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hr i.val))

/- Positive spectral blocks supported on an actual character projector have
at least the actual irreducible dimension. No decomposition is assumed. -/
lemma dimension_mul_eigenvalue_le_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (r : n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hτ : ∀ g, τ g * Matrix.diagonal (fun i => (r i : ℂ)) =
      Matrix.diagonal (fun i => (r i : ℂ)) * τ g)
    (hP : ρ.projector τ * Matrix.diagonal (fun i => (r i : ℂ)) = Matrix.diagonal (fun i => (r i : ℂ)))
    (i : n) : (ρ.dimension : ℝ)*r i ≤ ∑ j, r j := by
  by_cases hi : r i=0
  · simp only [hi,mul_zero]
    exact Finset.sum_nonneg (fun j _ => hr j)
  · let : Nonempty (Level r (r i)) := ⟨⟨i,rfl⟩⟩
    have hzero := offDiagonal_zero τ r hτ
    have hproj : ρ.projector (representation τ r (r i) hzero) = 1 := by
      rw [projector_representation]
      exact projector_on_level _ _ _ hi hP
    have hc := ρ.dimension_le_of_projector_one (representation τ r (r i) hzero) hproj
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hr i)).trans
      (level_card_le_trace r hr (r i))
end CoordinateSweeps.SpectralBlock

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

/- Source06's dimension-normalized spectral estimate, for every genuine
finite group representation. A is supported on the actual central projection. -/
theorem supported_trace_domination (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (hcomm : ∀ g, τ g * A = A * τ g) (hP : ρ.projector τ * A = A) :
    (Matrix.trace A • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let e := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star U)).toAlgEquiv.toAlgHom
  let r := hA.isHermitian.eigenvalues
  let d : n → ℂ := RCLike.ofReal ∘ r
  let τ' : Γ →* Matrix n n ℂ := e.toMonoidHom.comp τ
  have hdiag : e A = Matrix.diagonal d := hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hcomm' (g : Γ) : τ' g * Matrix.diagonal d = Matrix.diagonal d * τ' g := by
    change e (τ g) * Matrix.diagonal d = Matrix.diagonal d * e (τ g)
    rw [← hdiag,← map_mul,← map_mul,hcomm g]
  have hP' : ρ.projector τ' * Matrix.diagonal d = Matrix.diagonal d := by
    rw [ρ.projector_map e τ,← hdiag,← map_mul,hP]
  have hi (i : n) : (ρ.dimension : ℝ)*r i ≤ ∑ j, r j :=
    SpectralBlock.dimension_mul_eigenvalue_le_trace ρ τ' r hA.eigenvalues_nonneg hcomm' hP' i
  have hd (i : n) : (0 : ℂ) ≤ Matrix.trace A - (ρ.dimension : ℂ)*d i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    change (0 : ℂ) ≤ (∑ j, (r j : ℂ)) - (ρ.dimension : ℂ)*(r i : ℂ)
    exact_mod_cast sub_nonneg.mpr (hi i)
  have hD := Matrix.PosSemidef.diagonal hd
  have h := hD.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ).conjTranspose = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hspec : (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ).conjTranspose = A := by
    simpa only [U,d,r,Function.comp_def,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem.symm
  have he : Matrix.diagonal (fun i => Matrix.trace A - (ρ.dimension : ℂ)*d i) =
      Matrix.trace A • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • Matrix.diagonal d := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
  simpa only [he,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hU,hspec] using h

/- Compression of a positive invariant unit-trace operator to any isotypic
type is at most inverse irreducible dimension in operator order. -/
theorem invariant_projector_trace_domination (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (T : Matrix n n ℂ) (hT : T.PosSemidef)
    (hcomm : ∀ g, τ g*T=T*τ g) :
    (Matrix.trace T • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) •
      (ρ.projector τ * T * ρ.projector τ)).PosSemidef := by
  let P := ρ.projector τ
  have hP : P.conjTranspose=P := ρ.projector_hermitian τ hu
  have hP2 : P*P=P := ρ.projector_idempotent τ
  let A := P*T*P
  have hA : A.PosSemidef := by
    simpa only [hP] using hT.mul_mul_conjTranspose_same P
  have hAc (g : Γ) : τ g*A=A*τ g := by
    dsimp [A]
    calc
      _ = (τ g*P)*T*P := by noncomm_ring
      _ = (P*τ g)*T*P := by rw [ρ.projector_commute τ g]
      _ = P*(τ g*T)*P := by noncomm_ring
      _ = P*(T*τ g)*P := by rw [hcomm]
      _ = P*T*(τ g*P) := by noncomm_ring
      _ = P*T*(P*τ g) := by rw [ρ.projector_commute τ g]
      _ = _ := by noncomm_ring
  have hPA : P*A=A := by dsimp [A]; rw [← mul_assoc,← mul_assoc,hP2]
  have hbound := ρ.supported_trace_domination τ A hA hAc hPA
  have htrace : Matrix.trace A ≤ Matrix.trace T := by
    have hc := hT.mul_mul_conjTranspose_same (1-P)
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP] at hc
    have hh := hc.trace_nonneg
    have he : Matrix.trace ((1-P)*T*(1-P)) = Matrix.trace T-Matrix.trace A := by
      dsimp [A]
      have hx : (1-P)*(1-P) = 1-P := by
        calc
          _ = 1-P-P+P*P := by noncomm_ring
          _ = _ := by rw [hP2]; module
      rw [Matrix.trace_mul_cycle,hx,sub_mul,one_mul,Matrix.trace_sub]
      rw [Matrix.trace_mul_cycle P T P,hP2]

    rw [he] at hh
    exact sub_nonneg.mp hh
  have hpad := (Matrix.PosSemidef.one (n := n) (R := ℂ)).smul (sub_nonneg.mpr htrace)
  have h := hpad.add hbound
  change (Matrix.trace T • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • A).PosSemidef
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  module
end CoordinateSweeps.UnitaryIrrep
namespace CoordinateSweeps.Overlap
open TensorBoard
variable {n Γ : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Group Γ] [Fintype Γ]

open scoped MatrixOrder in
lemma norm_le_trace (A : Matrix n n ℂ) (hA : A.PosSemidef) : ‖A‖ ≤ (Matrix.trace A).re := by
  have hh := PositiveTensor.trace_domination A hA
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (show A ≤ Matrix.trace A • (1 : Matrix n n ℂ) from sub_nonneg.mp hh.nonneg) hA.nonneg
  have htr := Complex.nonneg_iff.mp hA.trace_nonneg
  have he : ((Matrix.trace A).re : ℂ)=Matrix.trace A := by
    apply Complex.ext <;> simp [htr.2]
  rw [← he,norm_smul,Complex.norm_of_nonneg htr.1,norm_one,mul_one] at hn
  exact hn

lemma norm_sq_le_trace (A : Matrix n n ℂ) :
    ‖A‖^2 ≤ (Matrix.trace (A.conjTranspose*A)).re := by
  have hh := norm_le_trace _ (Matrix.posSemidef_conjTranspose_mul_self A)
  simpa only [Matrix.l2_opNorm_conjTranspose_mul_self,pow_two] using hh

omit [DecidableEq n] [Nonempty n] in
lemma projection_product_posSemidef (P Q : Matrix n n ℂ)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hQ : Q.PosSemidef) (hPQ : P*Q=Q*P) :
    (P*Q).PosSemidef := by
  have hh := hQ.mul_mul_conjTranspose_same P
  rwa [hP.eq,hPQ,mul_assoc,hP2,← hPQ] at hh

lemma overlap_norm_sq_le_trace (R Q P : Matrix n n ℂ)
    (hR : R.IsHermitian) (hR2 : R*R=R) (hQ : Q.IsHermitian) (hQ2 : Q*Q=Q)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hPQ : P*Q=Q*P) :
    ‖Q*P*R‖^2 ≤ (Matrix.trace (R*(Q*P))).re := by
  have hh := norm_sq_le_trace (Q*P*R)
  have he : (Q*P*R).conjTranspose*(Q*P*R)=R*Q*P*R := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hR.eq,hP.eq,hQ.eq]
    calc
      _ = R*P*(Q*Q)*P*R := by noncomm_ring
      _ = R*(P*Q)*P*R := by rw [hQ2]; noncomm_ring
      _ = R*Q*(P*P)*R := by rw [hPQ]; noncomm_ring
      _ = _ := by rw [hP2]
  rw [he,mul_assoc R Q P,Matrix.trace_mul_cycle R (Q*P) R,hR2] at hh
  simpa only [mul_assoc] using hh

/- Whitening of genuine isotypic trace domination. All projections and
commutations are explicit algebraic obligations; no spectral conclusion assumed. -/
omit [Nonempty n] in
lemma whitened_projector_domination (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹)
    (T A Q : Matrix n n ℂ) (hT : T.PosSemidef)
    (hcomm : ∀ g, τ g*T=T*τ g) (hA : A.IsHermitian)
    (hATA : A*T*A=1) (hAP : A*ρ.projector τ=ρ.projector τ*A)
    (hAQ : A*Q=Q*A) (hQ : Q.IsHermitian) (hQ2 : Q*Q=Q)
    (hPQ : ρ.projector τ*Q= Q*ρ.projector τ) :
    (Matrix.trace T • (A*Q*A) - (ρ.dimension : ℂ) • (Q*ρ.projector τ)).PosSemidef := by
  let P := ρ.projector τ
  change A*P=P*A at hAP
  change P*Q=Q*P at hPQ
  have hP2 : P*P=P := ρ.projector_idempotent τ
  have hh := ρ.invariant_projector_trace_domination τ hu T hT hcomm
  change (Matrix.trace T • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • (P*T*P)).PosSemidef at hh
  have hk := (hh.mul_mul_conjTranspose_same Q).mul_mul_conjTranspose_same A
  simp only [hA.eq,hQ.eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] at hk
  have hAQP : A*(Q*P)=(Q*P)*A := by
    rw [← mul_assoc,hAQ,mul_assoc Q A P,hAP,← mul_assoc]
  have hPQA : (P*Q)*A=A*(P*Q) := by
    rw [mul_assoc,← hAQ,← mul_assoc P A Q,← hAP,mul_assoc]
  have ht : A*(Q*(P*T*P)*Q)*A=Q*P := by
    calc
      _ = (A*(Q*P))*T*((P*Q)*A) := by noncomm_ring
      _ = (Q*P)*(A*T*A)*(P*Q) := by rw [hAQP,hPQA]; noncomm_ring
      _ = Q*(P*P)*Q := by rw [hATA]; noncomm_ring
      _ = Q*(P*Q) := by rw [hP2,mul_assoc]
      _ = Q*(Q*P) := by rw [hPQ]
      _ = Q*P := by rw [← mul_assoc,hQ2]
  have he : A*(Q*1*Q)*A=A*Q*A := by rw [mul_one,hQ2]
  rw [he,ht] at hk
  exact hk

end CoordinateSweeps.Overlap

namespace CoordinateSweeps.Overlap
open TensorBoard
variable {n I J : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype I] [Fintype J]

omit [DecidableEq n] [Nonempty n] in
lemma trace_mixture_re (w : I → ℝ) (U : I → Matrix n n ℂ) (W : Matrix n n ℂ) :
    (Matrix.trace ((∑ i, (w i : ℂ) • U i)*W)).re = ∑ i, w i*(Matrix.trace (U i*W)).re := by
  simp only [Matrix.sum_mul,Matrix.smul_mul,Matrix.trace_sum,Matrix.trace_smul,Complex.re_sum,
    smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

omit [DecidableEq n] [Nonempty n] in
lemma trace_smul_re (t : ℝ) (W : Matrix n n ℂ) :
    (Matrix.trace ((t : ℂ) • W)).re=t*(Matrix.trace W).re := by
  simp [Matrix.trace_smul]

omit [DecidableEq n] [Nonempty n] in
lemma trace_four_swap (A Q U : Matrix n n ℂ) :
    Matrix.trace (A*Q*A*U)=Matrix.trace (A*U*A*Q) := by
  calc
    _ = Matrix.trace ((A*Q)*(A*U)) := congrArg Matrix.trace (by noncomm_ring)
    _ = Matrix.trace ((A*U)*(A*Q)) := Matrix.trace_mul_comm _ _
    _ = _ := congrArg Matrix.trace (by noncomm_ring)

/- Finite density mixtures plus genuine whitened isotypic domination give
the row-column overlap bound, before the harmless epsilon limit. -/
theorem finite_mixture_overlap (R Q P : Matrix n n ℂ)
    (hR : R.IsHermitian) (hR2 : R*R=R) (hQ : Q.IsHermitian) (hQ2 : Q*Q=Q)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hPQ : P*Q=Q*P)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (U : I → Matrix n n ℂ) (V : J → Matrix n n ℂ) (A : I → Matrix n n ℂ)
    (hU : ∀ i, (U i).PosSemidef) (hA : ∀ i, (A i).IsHermitian)
    (cr cc D t E : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • U i)-R).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • V j)-Q).PosSemidef)
    (hwhite : ∀ i, ((t : ℂ) • (A i*Q*A i)-(D : ℂ) • (Q*P)).PosSemidef)
    (hpair : ∀ i j, (Matrix.trace (A i*U i*A i*V j)).re ≤ E) :
    D*‖Q*P*R‖^2 ≤ cr*cc*t*E := by
  have hQpos : Q.PosSemidef := by
    simpa only [hQ.eq,hQ2] using Matrix.posSemidef_conjTranspose_mul_self Q
  have hQP : (Q*P).PosSemidef := by
    rw [← hPQ]
    exact projection_product_posSemidef P Q hP hP2 hQpos hPQ
  have hlocal (i : I) : D*(Matrix.trace (U i*(Q*P))).re ≤ t*cc*E := by
    let W := A i*U i*A i
    have hW : W.PosSemidef := by
      simpa only [(hA i).eq] using (hU i).mul_mul_conjTranspose_same (A i)
    have hc := (Complex.le_def.mp (trace_mono_right hcol hW)).1
    rw [Matrix.smul_mul,trace_smul_re,trace_mixture_re] at hc
    have hpair' (j : J) : (Matrix.trace (V j*W)).re ≤ E := by
      rw [Matrix.trace_mul_comm]
      exact hpair i j
    have hc' : (Matrix.trace (W*Q)).re ≤ cc*E := by
      rw [Matrix.trace_mul_comm]
      apply hc.trans
      apply mul_le_mul_of_nonneg_left _ hcc
      calc
        _ ≤ ∑ j, v j*E := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpair' j) (hv j))
        _ = E := by rw [← Finset.sum_mul,hsv,one_mul]
    have hw := (Complex.le_def.mp (trace_mono_right (hwhite i) (hU i))).1
    rw [Matrix.smul_mul,Matrix.smul_mul,trace_smul_re,trace_smul_re,
      trace_four_swap,Matrix.trace_mul_comm (Q*P)] at hw
    exact hw.trans (by simpa only [W,mul_assoc] using mul_le_mul_of_nonneg_left hc' ht)
  have hr := (Complex.le_def.mp (trace_mono_right hrow hQP)).1
  rw [Matrix.smul_mul,trace_smul_re,trace_mixture_re] at hr
  calc
    _ ≤ D*(Matrix.trace (R*(Q*P))).re := mul_le_mul_of_nonneg_left
      (overlap_norm_sq_le_trace R Q P hR hR2 hQ hQ2 hP hP2 hPQ) hD
    _ ≤ D*(cr*∑ i, u i*(Matrix.trace (U i*(Q*P))).re) := mul_le_mul_of_nonneg_left hr hD
    _ = cr*(∑ i, u i*(D*(Matrix.trace (U i*(Q*P))).re)) := by
      rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ cr*(∑ i, u i*(t*cc*E)) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlocal i) (hu i))) hcr
    _ = cr*cc*t*E := by rw [← Finset.sum_mul,hsu,one_mul]; ring

end CoordinateSweeps.Overlap

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
-- module Solutions.OAIQ56_CS.SignedTensor_Overlap
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
namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

omit [Nonempty R] in
lemma board_trace_le_reindexed {l : ℕ} (F : Finset (R × C)) (e : Fin l ≃ F)
    (r : R → Matrix J J ℂ) (v : C → Matrix J J ℂ)
    (hr : ∀ i, (r i).PosSemidef) (hv : ∀ j, (v j).PosSemidef)
    (ht : ∀ j, Matrix.trace (v j)=1) (A : Matrix J J ℂ) (hA : A.IsHermitian)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    (Matrix.trace (tensor (fun _ : Fin l => A)*tensor (fun x => r (e x).val.1)*
      tensor (fun _ : Fin l => A)*tensor (fun x => v (e x).val.2))).re ≤
        Real.exp (Fintype.card R*Fintype.card C-F.card) := by
  have hh := board_trace_le F r v hr hv ht A hA hw
  rw [← tensor_mul,tensor_trace] at hh
  rw [← tensor_mul,← tensor_mul,← tensor_mul,tensor_trace]
  have he := Equiv.prod_comp e (fun x : F => Matrix.trace (A*r x.val.1*A*v x.val.2))
  simpa only [he] using hh

end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]
lemma projector_commute_lift (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (x : MonoidAlgebra ℂ Γ) :
    ρ.projector τ*MonoidAlgebra.lift ℂ _ _ τ x=MonoidAlgebra.lift ℂ _ _ τ x*ρ.projector τ := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa using (ρ.projector_commute τ g).symm
  | add x y hx hy => simp only [map_add,add_mul,mul_add,hx,hy]
  | smul c x hx => simp only [map_smul,smul_mul_assoc,mul_smul_comm,hx]
end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.SignedTensor

lemma densityPower_commute_projector {p l : ℕ} (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : IsEven r) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    densityPower l r*ρ.projector (action p l)=ρ.projector (action p l)*densityPower l r := by
  simp only [UnitaryIrrep.projector,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact congrArg (fun A => ρ.coefficient σ • A) (densityPower_commute_of_even r hr σ).symm

lemma even_average_trace {R : Type*} [Fintype R] [Nonempty R] {p : ℕ}
    (r : R → EvenDensity p) (ε : ℝ) :
    Matrix.trace ((Fintype.card R : ℂ)⁻¹ • (∑ i, (r i).val)+
      (ε : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)) = 1+ε*(2*p) := by
  rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_sum,Matrix.trace_smul,Matrix.trace_one]
  simp only [(r _).property.2.1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    smul_eq_mul,Fintype.card_fin]
  have hc : (Fintype.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hc]
  push_cast
  rfl

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]
omit [Nonempty R] in
lemma board_trace_le_labels {l : ℕ} (e : Fin l → R × C) (he : Function.Injective e)
    (r : R → Matrix J J ℂ) (v : C → Matrix J J ℂ)
    (hr : ∀ i, (r i).PosSemidef) (hv : ∀ j, (v j).PosSemidef)
    (ht : ∀ j, Matrix.trace (v j)=1) (A : Matrix J J ℂ) (hA : A.IsHermitian)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    (Matrix.trace (tensor (fun _ : Fin l => A)*tensor (fun x => r (e x).1)*
      tensor (fun _ : Fin l => A)*tensor (fun x => v (e x).2))).re ≤
        Real.exp (Fintype.card R*Fintype.card C-l) := by
  let F : Finset (R × C) := Finset.univ.image e
  let E : Fin l ≃ F := Equiv.ofBijective (fun x => ⟨e x,by simp [F]⟩) (by
    constructor
    · intro x y h; exact he (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,_,hx⟩ := Finset.mem_image.mp y.property
      exact ⟨x,Subtype.ext hx⟩)
  have hc : F.card=l := by
    dsimp [F]
    rw [Finset.card_image_of_injective _ he,Finset.card_univ,Fintype.card_fin]
  have hh := board_trace_le_reindexed F E r v hr hv ht A hA hw
  have hE (x : Fin l) : (E x).val=e x := rfl
  simpa only [hE,hc] using hh
end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

theorem label_board_overlap_regularized {p l : ℕ} (hp : 0 < p)
    (e : Fin l → R × C) (hinj : Function.Injective e)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l)))
    (PR : Matrix (Word p l) (Word p l) ℂ) (xC : MonoidAlgebra ℂ (Equiv.Perm (Fin l)))
    (hPR : PR.IsHermitian) (hPR2 : PR*PR=PR)
    (hPC : (groupOperator (p := p) xC).IsHermitian)
    (hPC2 : groupOperator (p := p) xC*groupOperator (p := p) xC=groupOperator (p := p) xC)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (r : I → R → EvenDensity p) (c : J → C → EvenDensity p)
    (cr cc : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • labelRowProduct e (r i))-PR).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • labelColumnProduct e (c j))-groupOperator xC).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤
      cr*cc*(1+ε*(2*p : ℕ))^l*Real.exp (Fintype.card R*Fintype.card C-l) := by
  let : NeZero (2*p) := ⟨by omega⟩
  let τ := action p l
  let PC := groupOperator (p := p) xC
  let B (i : I) : Matrix (Letter p) (Letter p) ℂ :=
    (Fintype.card R : ℂ)⁻¹ • (∑ k, (r i k).val)+(ε : ℂ) • 1
  choose A hA hAe hABA hAw using fun i => exists_even_whitening (r i) hε
  have hb (i : I) : (B i).PosSemidef :=
    (average_regularization_posDef (fun k => (r i k).val) (fun k => (r i k).property.1) hε).posSemidef
  have he (i : I) : IsEven (B i) := isEven_add
    (isEven_smul _ (isEven_sum _ (fun k => (r i k).property.2.2))) (isEven_smul _ isEven_one)
  have htau (g : Equiv.Perm (Fin l)) : (τ g).conjTranspose=τ g⁻¹ := (matrix_inv g).symm
  have hpq : ρ.projector τ*PC=PC*ρ.projector τ := ρ.projector_commute_lift τ xC
  have htt : 0 ≤ (1+ε*(2*p : ℕ))^l := pow_nonneg (by positivity) _
  have hwhite (i : I) :
      (((1+ε*(2*p : ℕ))^l : ℝ) : ℂ) • (densityPower l (A i)*PC*densityPower l (A i)) -
        (ρ.dimension : ℂ) • (PC*ρ.projector τ) |>.PosSemidef := by
    have hWA : (densityPower l (A i)).IsHermitian := (densityPower_posSemidef l (A i) (hA i)).isHermitian
    have hWABA : densityPower l (A i)*densityPower l (B i)*densityPower l (A i)=1 := by
      rw [← densityPower_mul,← densityPower_mul,hABA i,densityPower_one]
    have hh := Overlap.whitened_projector_domination ρ τ htau
      (densityPower l (B i)) (densityPower l (A i)) PC (densityPower_posSemidef l (B i) (hb i))
      (fun g => densityPower_commute_of_even (B i) (he i) g) hWA hWABA
      (densityPower_commute_projector (A i) (hAe i) ρ)
      (densityPower_commute_lift (A i) (hAe i) xC).symm hPC hPC2 hpq
    have ht : Matrix.trace (densityPower l (B i))=(((1+ε*(2*p : ℕ))^l : ℝ) : ℂ) := by
      rw [densityPower_trace,even_average_trace]
      push_cast
      rfl
    rwa [ht] at hh
  apply Overlap.finite_mixture_overlap PR PC (ρ.projector τ) hPR hPR2 hPC hPC2
    (ρ.projector_hermitian τ htau) (ρ.projector_idempotent τ) hpq u v hu hv hsu hsv
    (fun i => labelRowProduct e (r i)) (fun j => labelColumnProduct e (c j)) (fun i => densityPower l (A i))
    (fun i => TensorBoard.tensor_posSemidef _ (fun x => (r i (e x).1).property.1))
    (fun i => (densityPower_posSemidef l (A i) (hA i)).isHermitian)
    cr cc ρ.dimension ((1+ε*(2*p : ℕ))^l) _ hcr hcc (Nat.cast_nonneg _) htt hrow hcol hwhite
  intro i j
  exact board_trace_le_labels e hinj (fun k => (r i k).val) (fun k => (c j k).val)
    (fun k => (r i k).property.1) (fun k => (c j k).property.1) (fun k => (c j k).property.2.1)
    (A i) (hA i).isHermitian (hAw i)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard Overlap
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

theorem label_board_overlap {p l : ℕ} (hp : 0 < p)
    (e : Fin l → R × C) (hinj : Function.Injective e)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l)))
    (PR : Matrix (Word p l) (Word p l) ℂ) (xC : MonoidAlgebra ℂ (Equiv.Perm (Fin l)))
    (hPR : PR.IsHermitian) (hPR2 : PR*PR=PR)
    (hPC : (groupOperator (p := p) xC).IsHermitian)
    (hPC2 : groupOperator (p := p) xC*groupOperator (p := p) xC=groupOperator (p := p) xC)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (r : I → R → EvenDensity p) (c : J → C → EvenDensity p)
    (cr cc : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • labelRowProduct e (r i))-PR).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • labelColumnProduct e (c j))-groupOperator xC).PosSemidef)
 :
    (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤
      cr*cc*Real.exp (Fintype.card R*Fintype.card C-l) := by
  let f (ε : ℝ) := cr*cc*(1+ε*(2*p : ℕ))^l*Real.exp (Fintype.card R*Fintype.card C-l)
  have hf : Continuous f := by fun_prop
  have hh : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (ρ.dimension : ℝ)*‖groupOperator (p := p) xC*ρ.projector (action p l)*PR‖^2 ≤ f ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact label_board_overlap_regularized hp e hinj ρ PR xC hPR hPR2 hPC hPC2
      u v hu hv hsu hsv r c cr cc hcr hcc hrow hcol hε
  have hh' := ge_of_tendsto (hf.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)) hh
  simpa [f] using hh'

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {p r c : ℕ} [NeZero r]
  {L : Type*} [Fintype L] [DecidableEq L]

/- Source 06:eq19 for literal row and column subgroup projectors on an
arbitrary board with holes. The mixtures and signed regroupings are constructed. -/
omit [DecidableEq L] in
theorem actual_label_overlap (f : L → Fin r) (g : L → Fin c)
    (hinj : Function.Injective (fun x => (f x,g x)))
    (e : Fin (Fintype.card L) ≃ L) (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hnR : ∀ i, FiberBlocks.size f i ≤ s)
    (hnC : ∀ j, FiberBlocks.size g j ≤ s)
    (ρR : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i))))
    (ρC : ∀ j, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size g j))))
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) :
    (ρ.dimension : ℝ)*‖fiberProjector (p := p) g e ρC*
      ρ.projector (action p (Fintype.card L))*fiberProjector f e ρR‖^2 ≤
        ((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)))*
        ((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2)))*
        Real.exp (r*c-Fintype.card L) := by
  obtain ⟨I,hI,nI,a,ha⟩ := finite_fiber_density_domination f e s hp hps hnR ρR
  obtain ⟨J,hJ,nJ,b,hb⟩ := finite_fiber_density_domination g e s hp hps hnC ρC
  let := hI
  let := hJ
  let := nI
  let := nJ
  have hI0 : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hu : ∑ _ : I, (Fintype.card I : ℝ)⁻¹=1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ hI0]
  have hv : ∑ _ : J, (Fintype.card J : ℝ)⁻¹=1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ hJ0]
  have hr := fiberProjector_posSemidef (p := p) f e ρR
  have hc := fiberProjector_posSemidef (p := p) g e ρC
  have hr2 := fiberProjector_idempotent (p := p) f e ρR
  have hc2 := fiberProjector_idempotent (p := p) g e ρC
  let xC := fiberProjectorAlgebra g e ρC
  have hx : groupOperator (p := p) xC=fiberProjector (p := p) g e ρC :=
    fiberProjectorAlgebra_lift _ _ _
  have hrow : (((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)) : ℝ) : ℂ) •
      (∑ i : I, (((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • labelRowProduct (fun x => (f (e x),g (e x))) (a i))-
        fiberProjector (p := p) f e ρR |>.PosSemidef := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_inv,← Finset.smul_sum,labelRowProduct] using ha
  have hcol : (((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2)) : ℝ) : ℂ) •
      (∑ j : J, (((Fintype.card J : ℝ)⁻¹ : ℝ) : ℂ) • labelColumnProduct (fun x => (f (e x),g (e x))) (b j))-
        groupOperator (p := p) xC |>.PosSemidef := by
    rw [hx]
    simpa only [Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_inv,← Finset.smul_sum,labelColumnProduct] using hb
  have hh := label_board_overlap hp (fun x => (f (e x),g (e x))) (hinj.comp e.injective) ρ _ xC hr.isHermitian hr2 (hx ▸ hc.isHermitian)
    (by rw [hx]; exact hc2) (fun _ : I => (Fintype.card I : ℝ)⁻¹)
    (fun _ : J => (Fintype.card J : ℝ)⁻¹) (fun _ => by positivity) (fun _ => by positivity)
    hu hv a b ((∏ i, ((ρR i).dimension : ℝ))*(s+1 : ℕ)^(r*(41*p^2)))
    ((∏ j, ((ρC j).dimension : ℝ))*(s+1 : ℕ)^(c*(41*p^2))) (by positivity) (by positivity) hrow hcol
  simpa only [hx,Fintype.card_fin] using hh

end CoordinateSweeps.SignedTensor

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
-- module Solutions.OAIQ56_CS.Young_Classification
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
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.YoungCorner

lemma strictMono_fin_nat_ge {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) : i.val ≤ f i := by
  suffices hh : ∀ k, ∀ h : k < n, k ≤ f ⟨k,h⟩ from hh i.val i.isLt
  intro k
  induction k with
  | zero => intro h; exact Nat.zero_le _
  | succ k ih =>
    intro h
    have hk : k < n := by omega
    have hh := hf (show (⟨k,hk⟩ : Fin n) < ⟨k+1,h⟩ from by simp)
    have hi := ih hk
    omega

lemma sortPerm_ge {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) (i : Fin n) :
    i.val ≤ f (sortPerm f hf i) := by
  have he : f (sortPerm f hf i) = ((values f).orderEmbOfFin (values_card f hf)) i := by
    have hh := (valuesEquiv f hf).apply_symm_apply (((values f).orderIsoOfFin (values_card f hf)) i)
    exact congrArg Subtype.val hh
  rw [he]
  exact strictMono_fin_nat_ge _ ((values f).orderEmbOfFin (values_card f hf)).strictMono i

/- Row-column noncollision: at most one source cell in any row can land in
any destination column. -/

lemma sortingRows_mem (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ) :
    sortingRows μ σ h ∈ rows μ := by
  intro x
  rfl

lemma sortingRows_col_ge (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ)
    (x : Boxes μ) : x.val.2 ≤ (σ (sortingRows μ σ h x)).val.2 := by
  exact sortPerm_ge (rowColumn μ σ ⟨x.val.1,row_lt μ x⟩)
    (rowColumn_injective μ σ h _) ⟨x.val.2,col_lt μ x⟩

/- The essential Ferrers uniqueness lemma. Sorting inside rows can only
increase columns; preservation of the total column sum forces equality. -/
theorem factor_column_row (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ) :
    ∃ c ∈ cols μ, ∃ r ∈ rows μ, σ=c*r := by
  let r := sortingRows μ σ h
  have hr : r ∈ rows μ := sortingRows_mem μ σ h
  have hge : ∀ x : Boxes μ, x.val.2 ≤ ((σ*r) x).val.2 := sortingRows_col_ge μ σ h
  have hsum : ∑ x : Boxes μ, x.val.2 = ∑ x : Boxes μ, ((σ*r) x).val.2 :=
    (Fintype.sum_equiv (σ*r) (fun x : Boxes μ => ((σ*r) x).val.2)
      (fun x : Boxes μ => x.val.2) (fun _ => rfl)).symm
  have heq : ∀ x : Boxes μ, x.val.2=((σ*r) x).val.2 := by
    intro x
    exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hge x)).mp hsum x (Finset.mem_univ _)
  refine ⟨σ*r,(fun x => (heq x).symm),r⁻¹,(rows μ).inv_mem hr,?_⟩
  simp

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma card_column_prefix (μ : YoungDiagram) (t j : ℕ) :
    ((rowPrefix μ t).filter (fun x => x.val.2=j)).card=min t (μ.colLen j) := by
  have h := Fintype.card_congr (columnPrefixEquiv μ t j)
  simpa only [Fintype.card_coe,Fintype.card_fin] using h

lemma card_source_column_le (μ ν : YoungDiagram) (e : Boxes μ ≃ Boxes ν)
    (hnc : ∀ x y, x.val.1=y.val.1 → (e x).val.2=(e y).val.2 → x=y) (t j : ℕ) :
    ((rowPrefix μ t).filter (fun x => (e x).val.2=j)).card ≤ min t (ν.colLen j) := by
  let F := (rowPrefix μ t).filter (fun x => (e x).val.2=j)
  have hr : F.card≤t := by
    let f : ↥F → Fin t := fun x => ⟨x.val.val.1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp x.property).1).2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply hnc
      · exact congrArg Fin.val hxy
      · exact (Finset.mem_filter.mp x.property).2.trans (Finset.mem_filter.mp y.property).2.symm
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hc : F.card≤ν.colLen j := by
    let f : ↥F → Fin (ν.colLen j) := fun x => ⟨(e x.val).val.1,by
      have hx := YoungDiagram.mem_iff_lt_colLen.mp (e x.val).property
      rw [(Finset.mem_filter.mp x.property).2] at hx
      exact hx⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Fin.val hxy
      · exact (Finset.mem_filter.mp x.property).2.trans (Finset.mem_filter.mp y.property).2.symm
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact le_min hr hc

/- The actual Ferrers dominance consequence of a collision-free matching. -/
theorem prefix_dominance (μ ν : YoungDiagram) (e : Boxes μ ≃ Boxes ν)
    (hnc : ∀ x y, x.val.1=y.val.1 → (e x).val.2=(e y).val.2 → x=y) (t : ℕ) :
    (rowPrefix μ t).card≤(rowPrefix ν t).card := by
  have hμ : Set.MapsTo (fun x : Boxes μ => (e x).val.2) (rowPrefix μ t)
      (Finset.range (ν.rowLen 0)) := by
    intro x hx
    exact Finset.mem_range.mpr ((col_lt ν (e x)).trans_le (ν.rowLen_anti _ _ (Nat.zero_le _)))
  have hν : Set.MapsTo (fun x : Boxes ν => x.val.2) (rowPrefix ν t)
      (Finset.range (ν.rowLen 0)) := by
    intro x hx
    exact Finset.mem_range.mpr ((col_lt ν x).trans_le (ν.rowLen_anti _ _ (Nat.zero_le _)))
  rw [Finset.card_eq_sum_card_fiberwise hμ,Finset.card_eq_sum_card_fiberwise hν]
  apply Finset.sum_le_sum
  intro j hj
  rw [card_column_prefix]
  exact card_source_column_le μ ν e hnc t j

lemma card_row (μ : YoungDiagram) (i : ℕ) :
    (Finset.univ.filter (fun x : Boxes μ => x.val.1=i)).card=μ.rowLen i := by
  have h := Fintype.card_congr (rowEquiv μ i)
  rw [Fintype.card_subtype] at h
  simpa only [Fintype.card_fin] using h

lemma prefix_succ (μ : YoungDiagram) (t : ℕ) :
    (rowPrefix μ (t+1)).card=(rowPrefix μ t).card+μ.rowLen t := by
  have he : rowPrefix μ (t+1)=rowPrefix μ t ∪ Finset.univ.filter (fun x : Boxes μ => x.val.1=t) := by
    ext x
    simp only [rowPrefix,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    omega
  have hd : Disjoint (rowPrefix μ t) (Finset.univ.filter (fun x : Boxes μ => x.val.1=t)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxt := (Finset.mem_filter.mp hx).2
    have hyt := (Finset.mem_filter.mp hy).2
    omega
  rw [he,Finset.card_union_of_disjoint hd,card_row]

/- Opposite Young dominance determines the diagram. -/
lemma eq_of_prefix_dominance (μ ν : YoungDiagram)
    (hμν : ∀ t, (rowPrefix μ t).card≤(rowPrefix ν t).card)
    (hνμ : ∀ t, (rowPrefix ν t).card≤(rowPrefix μ t).card) : μ=ν := by
  have he (t : ℕ) : (rowPrefix μ t).card=(rowPrefix ν t).card := le_antisymm (hμν t) (hνμ t)
  have hr (t : ℕ) : μ.rowLen t=ν.rowLen t := by
    have hh := he (t+1)
    rw [prefix_succ,prefix_succ,he t] at hh
    omega
  apply SetLike.ext
  rintro ⟨i,j⟩
  simp only [YoungDiagram.mem_iff_lt_rowLen,hr]

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RepDetection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/- Irreducibility supplies the cross-corner nonvanishing needed for Young
shape uniqueness via the orbit-span argument. -/
theorem exists_cross_nonzero (τ : Representation ℂ G V) [τ.IsIrreducible]
    (P Q : Module.End ℂ V) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ g, P * τ g * Q ≠ 0 := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, Q v ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (LinearMap.ext h)
  let S : Subrepresentation τ :=
    { toSubmodule := Submodule.span ℂ (Set.range (fun g => τ g (Q v)))
      apply_mem_toSubmodule := by
        intro g w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k,rfl⟩ := hw
          apply Submodule.subset_span
          exact ⟨g*k,by simp only [map_mul,Module.End.mul_apply]⟩
        | zero => simp
        | add x y hx hy ix iy => simpa using Submodule.add_mem _ ix iy
        | smul c x hx ix => simpa using Submodule.smul_mem _ c ix }
  have hSne : S ≠ ⊥ := by
    intro hs
    have hm : Q v ∈ S := by
      apply Submodule.subset_span
      exact ⟨1,by simp⟩
    rw [hs] at hm
    exact hv hm
  have hStop : S=⊤ := (eq_bot_or_eq_top S).resolve_left hSne
  by_contra hn
  push Not at hn
  have hs : S.toSubmodule ≤ LinearMap.ker P := by
    apply Submodule.span_le.mpr
    rintro x ⟨g,rfl⟩
    have hh := congrArg (fun (A : Module.End ℂ V) => A v) (hn g)
    exact hh
  rw [hStop] at hs
  apply hP
  apply LinearMap.ext
  intro x
  exact hs Submodule.mem_top

end CoordinateSweeps.RepDetection

namespace CoordinateSweeps.YoungCorner
variable {X A : Type*} [Fintype X] [DecidableEq X] [Ring A] [Algebra ℂ A]

/- Ordinary source sign. -/
omit [Algebra ℂ A] in
lemma fixedSum_right (f : X → ℕ) (ρ : Equiv.Perm X →* A)
    (r : colorStabilizer f) : fixedSum f ρ * ρ r = fixedSum f ρ := by
  rw [fixedSum,Finset.sum_mul]
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight r) _ _ (fun _ => rfl)

lemma alternatingSum_left (f : X → ℕ) (ρ : Equiv.Perm X →* A)
    (c : colorStabilizer f) : ρ c * alternatingSum f ρ = (signScalar (c : Equiv.Perm X))⁻¹ • alternatingSum f ρ := by
  rw [alternatingSum,Finset.mul_sum,Finset.smul_sum]
  have hc : signScalar (c : Equiv.Perm X) ≠ 0 := by
    intro hzero
    have hh : signScalar (c : Equiv.Perm X)*signScalar (c : Equiv.Perm X)⁻¹=1 := by
      rw [← map_mul,mul_inv_cancel,map_one]
    rw [hzero,zero_mul] at hh
    exact zero_ne_one hh
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro d
  change ρ (c : Equiv.Perm X) * (signScalar (d : Equiv.Perm X) • ρ (d : Equiv.Perm X)) =
    (signScalar (c : Equiv.Perm X))⁻¹ • (signScalar ((c : Equiv.Perm X) * (d : Equiv.Perm X)) • ρ ((c : Equiv.Perm X) * (d : Equiv.Perm X)))
  rw [mul_smul_comm,smul_smul,map_mul,map_mul,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

omit [Fintype X] in
lemma swap_mem_color (f : X → ℕ) (x y : X) (h : f x=f y) :
    Equiv.swap x y ∈ colorStabilizer f := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

/- Literal transposition cancellation in a Young row/column corner. -/
lemma colored_corner_zero (f g : X → ℕ) (ρ : Equiv.Perm X →* A)
    (σ : Equiv.Perm X) (x y : X) (hxy : x ≠ y)
    (hrow : f x=f y) (hcol : g (σ⁻¹ x)=g (σ⁻¹ y)) :
    fixedSum f ρ * ρ σ * alternatingSum g ρ=0 := by
  let r : colorStabilizer f := ⟨Equiv.swap x y,swap_mem_color f x y hrow⟩
  let c : colorStabilizer g := ⟨Equiv.swap (σ⁻¹ x) (σ⁻¹ y),swap_mem_color g _ _ hcol⟩
  have hcxy : σ⁻¹ x ≠ σ⁻¹ y := fun h => hxy ((σ⁻¹).injective h)
  have he : (r : Equiv.Perm X)*σ = σ*(c : Equiv.Perm X) := by
    apply Equiv.ext
    intro z
    change Equiv.swap x y (σ z) = σ (Equiv.swap (σ⁻¹ x) (σ⁻¹ y) z)
    by_cases hx : z=σ⁻¹ x
    · subst z; simp
    by_cases hy : z=σ⁻¹ y
    · subst z; simp
    have hx' : σ z ≠ x := by
      intro he; apply hx
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    have hy' : σ z ≠ y := by
      intro he; apply hy
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    rw [Equiv.swap_apply_of_ne_of_ne hx hy,Equiv.swap_apply_of_ne_of_ne hx' hy']
  have hc : (signScalar (c : Equiv.Perm X))⁻¹ = -1 := by rw [show (c : Equiv.Perm X)=Equiv.swap (σ⁻¹ x) (σ⁻¹ y) from rfl,signScalar_swap _ _ hcxy]; norm_num
  have hh : fixedSum f ρ * ρ σ * alternatingSum g ρ = -(fixedSum f ρ * ρ σ * alternatingSum g ρ) := by
    calc
      _ = (fixedSum f ρ * ρ r)*ρ σ*alternatingSum g ρ := by rw [fixedSum_right]
      _ = fixedSum f ρ * (ρ σ * ρ c) * alternatingSum g ρ := by rw [mul_assoc (fixedSum f ρ) (ρ r) (ρ σ),← map_mul,he,map_mul]
      _ = fixedSum f ρ * ρ σ * (ρ c * alternatingSum g ρ) := by simp only [mul_assoc]
      _ = _ := by rw [alternatingSum_left,hc]; simp
  have htwo : (2 : ℂ) • (fixedSum f ρ * ρ σ * alternatingSum g ρ)=0 := by
    rw [two_smul,← eq_neg_iff_add_eq_zero]
    exact hh
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X V : Type*} [Fintype X] [DecidableEq X] [AddCommGroup V] [Module ℂ V]

lemma cross_dominance (μ ν : YoungDiagram) (t : X ≃ Boxes μ) (u : X ≃ Boxes ν)
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible]
    (hP : fixedSum (rowColor t) τ ≠ 0) (hQ : alternatingSum (colColor u) τ ≠ 0) (k : ℕ) :
    (rowPrefix μ k).card≤(rowPrefix ν k).card := by
  obtain ⟨σ,hσ⟩ := RepDetection.exists_cross_nonzero τ _ _ hP hQ
  let e : Boxes μ ≃ Boxes ν := (t.symm.trans σ.symm).trans u
  apply prefix_dominance μ ν e _ k
  intro x y hrow hcol
  apply t.symm.injective
  by_contra hxy
  apply hσ
  apply colored_corner_zero (rowColor t) (colColor u) τ σ (t.symm x) (t.symm y) hxy
  · simpa [rowColor] using hrow
  · exact hcol

/- A genuine irreducible cannot carry two different Young shapes. -/
theorem shape_unique (μ ν : YoungDiagram) (t : X ≃ Boxes μ) (u : X ≃ Boxes ν)
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible]
    (hμ : hasShape μ t τ) (hν : hasShape ν u τ) : μ=ν := by
  have hPμ : fixedSum (rowColor t) τ ≠ 0 := left_ne_zero_of_mul hμ
  have hQμ : alternatingSum (colColor t) τ ≠ 0 := right_ne_zero_of_mul hμ
  have hPν : fixedSum (rowColor u) τ ≠ 0 := left_ne_zero_of_mul hν
  have hQν : alternatingSum (colColor u) τ ≠ 0 := right_ne_zero_of_mul hν
  exact eq_of_prefix_dominance μ ν
    (cross_dominance μ ν t u τ hPμ hQν) (cross_dominance ν μ u t τ hPν hQμ)

lemma hasShape_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    (μ : YoungDiagram) (t : X ≃ Boxes μ)
    (τ : Representation ℂ (Equiv.Perm X) V) (σ : Representation ℂ (Equiv.Perm X) W)
    (e : Representation.Equiv τ σ) (h : hasShape μ t τ) : hasShape μ t σ := by
  have hg (g : Equiv.Perm X) : e.toLinearEquiv.conjAlgEquiv ℂ (τ g)=σ g :=
    Representation.Equiv.conj_apply_self g e
  have he : e.toLinearEquiv.conjAlgEquiv ℂ (fixedSum (rowColor t) τ * alternatingSum (colColor t) τ)=
      fixedSum (rowColor t) σ * alternatingSum (colColor t) σ := by
    simp only [fixedSum,alternatingSum,map_mul,map_sum,map_smul,hg]
  intro hz
  apply h
  apply (e.toLinearEquiv.conjAlgEquiv ℂ).injective
  rw [he,hz,map_zero]

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X V : Type*} [Fintype X] [DecidableEq X] [AddCommGroup V] [Module ℂ V]

lemma shapeSubrep_hasShape (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    hasShape μ t (shapeSubrep μ t).toRepresentation :=
  (Classical.choose_spec (exists_shape_constituent μ t)).2

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma diagramOfPartition_injective {n : ℕ} : Function.Injective (@diagramOfPartition n) := by
  intro p q hpq
  apply Nat.Partition.ext
  have hh := congrArg YoungDiagram.rowLens hpq
  rw [diagramOfPartition_rowLens,diagramOfPartition_rowLens] at hh
  have hm := congrArg (fun t : List ℕ => (t : Multiset ℕ)) hh
  simpa only [Multiset.sort_eq] using hm

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.CharacterCount
universe u v w
variable {G : Type u} [Group G] [Fintype G]
variable {I : Type v} (V : I → Type w) [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
  (τ : ∀ i, Representation ℂ G (V i)) [∀ i, (τ i).IsIrreducible]

lemma characters_independent
    (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (τ i) (τ j))) :
    LinearIndependent ℂ (fun i => (τ i).character) := by
  classical
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hp (i j : I) : pairing V τ i (τ j).character=if j=i then 1 else 0 := by
    change (Fintype.card G : ℂ)⁻¹ * _ = _
    have hh := Representation.char_orthonormal (τ j) (τ i)
    rw [Nat.card_eq_fintype_card] at hh
    by_cases he : j=i
    · subst j
      have hi : Nonempty (Representation.Equiv (τ i) (τ i)) := ⟨Representation.Equiv.refl _⟩
      simpa [hi] using hh
    · have hi : ¬Nonempty (Representation.Equiv (τ i) (τ j)) := by
        intro ⟨e⟩
        exact (hne i j (Ne.symm he)).false e
      simpa [he,hi] using hh
  apply linearIndependent_iff'.mpr
  intro s c hs i hi
  have hh := congrArg (pairing V τ i) hs
  simp only [map_sum,map_smul,map_zero,hp,smul_eq_mul,mul_ite,mul_one,mul_zero] at hh
  simpa [hi] using hh

/- Pulling characters through any finite conjugacy classifier bounds how many
inequivalent irreducibles there can be. The classifier need not be surjective. -/
theorem card_le_of_classifier [Fintype I] {C : Type*} [Fintype C]
    (classifier : G → C)
    (hclass : ∀ i g h, classifier g=classifier h → (τ i).character g=(τ i).character h)
    (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (τ i) (τ j))) :
    Fintype.card I ≤ Fintype.card C := by
  classical
  let f : I → C → ℂ := fun i c =>
    if h : ∃ g, classifier g=c then (τ i).character (Classical.choose h) else 0
  have hf (i : I) (g : G) : f i (classifier g)=(τ i).character g := by
    dsimp [f]
    rw [dite_eq_left ⟨g,rfl⟩]
    exact hclass i _ _ (Classical.choose_spec (show ∃ k, classifier k=classifier g from ⟨g,rfl⟩))
  let L : (C → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f => f ∘ classifier
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : (L ∘ f)=(fun i => (τ i).character) := by funext i g; exact hf i g
  have hind : LinearIndependent ℂ f := LinearIndependent.of_comp L
    (he ▸ characters_independent V τ hne)
  have hh := hind.fintype_card_le_finrank
  simpa using hh

end CoordinateSweeps.CharacterCount

namespace CoordinateSweeps.CharacterCount
universe u w
variable {G C : Type u} [Group G] [Fintype G] [Fintype C]
  (V : C → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (τ : ∀ i, Representation ℂ G (V i)) [∀ i, (τ i).IsIrreducible]

/- An inequivalent family as large as a finite conjugacy classifier is complete.
This finite counting argument establishes the Young classification. -/
theorem complete_of_classifier (classifier : G → C)
    (hτ : ∀ i g h, classifier g=classifier h → (τ i).character g=(τ i).character h)
    (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (τ i) (τ j)))
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (hσ : ∀ g h, classifier g=classifier h → σ.character g=σ.character h) :
    ∃ i, Nonempty (Representation.Equiv (τ i) σ) := by
  classical
  by_contra hn
  push Not at hn
  let E : Option C → Type w := fun i => match i with | none => W | some i => V i
  let : ∀ i, AddCommGroup (E i) := fun i => by cases i <;> dsimp [E] <;> infer_instance
  let : ∀ i, Module ℂ (E i) := fun i => by cases i <;> dsimp [E] <;> infer_instance
  let : ∀ i, FiniteDimensional ℂ (E i) := fun i => by cases i <;> dsimp [E] <;> infer_instance
  let υ : ∀ i, Representation ℂ G (E i) := fun i => match i with | none => σ | some i => τ i
  let : ∀ i, (υ i).IsIrreducible := fun i => by cases i <;> dsimp [υ] <;> infer_instance
  have huclass : ∀ i g h, classifier g=classifier h → (υ i).character g=(υ i).character h := by
    intro i g h he
    cases i with
    | none => exact hσ g h he
    | some i => exact hτ i g h he
  have hune : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (υ i) (υ j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact ⟨fun e => (hn j).false e.symm⟩
    | some i =>
      cases j with
      | none => exact ⟨fun e => (hn i).false e⟩
      | some j => exact hne i j (fun he => hij (congrArg some he))
  have hh := card_le_of_classifier E υ classifier huclass hune
  simp only [Fintype.card_option] at hh
  omega

lemma permutation_character_factors {X V : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Equiv.Perm X) V)
    (g h : Equiv.Perm X) (he : g.partition=h.partition) : τ.character g=τ.character h := by
  obtain ⟨c,hc⟩ := isConj_iff.mp (Equiv.Perm.partition_eq_of_isConj.mpr he)
  rw [← hc,τ.char_conj]

end CoordinateSweeps.CharacterCount

namespace CoordinateSweeps.YoungCorner
variable {X : Type} [Fintype X] [DecidableEq X]

lemma partitionRep_hasShape (p : Nat.Partition (Fintype.card X)) :
    hasShape (diagramOfPartition p) (partitionFilling p (X := X)) (partitionRep p (X := X)) :=
  shapeSubrep_hasShape _ _

lemma partitionRep_inequivalent (p q : Nat.Partition (Fintype.card X)) (hpq : p ≠ q) :
    IsEmpty (Representation.Equiv (partitionRep p (X := X)) (partitionRep q (X := X))) := by
  refine ⟨fun e => ?_⟩
  apply hpq
  apply diagramOfPartition_injective
  exact shape_unique _ _ (partitionFilling p) (partitionFilling q) (partitionRep q)
    (hasShape_equiv _ _ _ _ e (partitionRep_hasShape p)) (partitionRep_hasShape q)

/- Young classification from regular constituents, Ferrers dominance and
finite-group character orthogonality. -/
theorem partitionRep_complete {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible] :
    ∃ p : Nat.Partition (Fintype.card X),
      Nonempty (Representation.Equiv (partitionRep p (X := X)) τ) := by
  let E : Nat.Partition (Fintype.card X) → Type := fun p => ↥(PartitionSpace (X := X) p)
  let υ : (p : Nat.Partition (Fintype.card X)) → Representation ℂ (Equiv.Perm X) (E p) :=
    fun p => partitionRep (X := X) p
  have hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (υ i) (υ j)) := by
    intro i j hij
    exact partitionRep_inequivalent (X := X) i j hij
  have hc : ∀ i g h, g.partition=h.partition → (υ i).character g=(υ i).character h :=
    fun i g h he => CharacterCount.permutation_character_factors (υ i) g h he
  exact CharacterCount.complete_of_classifier E υ Equiv.Perm.partition hc hne τ
    (CharacterCount.permutation_character_factors τ)

/- Every literal irreducible carries exactly one diagram shape. -/
theorem exists_partitionShape {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible] :
    ∃ p : Nat.Partition (Fintype.card X), hasShape (diagramOfPartition p) (partitionFilling p) τ := by
  obtain ⟨p,⟨e⟩⟩ := partitionRep_complete τ
  exact ⟨p,hasShape_equiv _ _ _ _ e (partitionRep_hasShape p)⟩

/- Two actual irreps of the same diagram are equivalent, even for unrelated
fillings. This is the uniqueness fact needed for the hook/removal argument. -/
theorem equiv_of_same_shape {V W : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ (Equiv.Perm X) V) (σ : Representation ℂ (Equiv.Perm X) W)
    [τ.IsIrreducible] [σ.IsIrreducible]
    (μ : YoungDiagram) (t u : X ≃ Boxes μ) (hτ : hasShape μ t τ) (hσ : hasShape μ u σ) :
    Nonempty (Representation.Equiv τ σ) := by
  obtain ⟨p,⟨ep⟩⟩ := partitionRep_complete τ
  obtain ⟨q,⟨eq⟩⟩ := partitionRep_complete σ
  have hp : μ=diagramOfPartition p := shape_unique _ _ t (partitionFilling p) τ hτ
    (hasShape_equiv _ _ _ _ ep (partitionRep_hasShape p))
  have hq : μ=diagramOfPartition q := shape_unique _ _ u (partitionFilling q) σ hσ
    (hasShape_equiv _ _ _ _ eq (partitionRep_hasShape q))
  have hpq : p=q := diagramOfPartition_injective (hp.symm.trans hq)
  subst q
  exact ⟨ep.symm.trans eq⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable (X : Type) [Fintype X] [DecidableEq X]

lemma partitionUnitary_equiv (p : Nat.Partition (Fintype.card X)) :
    Nonempty (Representation.Equiv (partitionRep p (X := X))
      (partitionUnitary X p).asRepresentation) :=
  Classical.choose_spec (UnitaryRealization.exists_unitary (partitionRep p (X := X)))

lemma partitionUnitary_inequivalent (p q : Nat.Partition (Fintype.card X)) (hpq : p ≠ q) :
    ¬Nonempty (Representation.Equiv (partitionUnitary X p).asRepresentation
      (partitionUnitary X q).asRepresentation) := by
  rintro ⟨e⟩
  obtain ⟨ep⟩ := partitionUnitary_equiv X p
  obtain ⟨eq⟩ := partitionUnitary_equiv X q
  exact (partitionRep_inequivalent p q hpq).false ((ep.trans e).trans eq.symm)

lemma partitionUnitary_complete {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible] :
    ∃ p, Nonempty (Representation.Equiv (partitionUnitary X p).asRepresentation τ) := by
  obtain ⟨p,⟨e⟩⟩ := partitionRep_complete τ
  obtain ⟨ep⟩ := partitionUnitary_equiv X p
  exact ⟨p,⟨ep.symm.trans e⟩⟩

/- The chosen Young projectors resolve identity in every finite representation.
The proof detects a simple constituent if the residual operator is nonzero. -/
theorem partition_projector_resolution {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm X) V) :
    ∑ p, (partitionUnitary X p).projector τ=1 := by
  by_contra hn
  have hz : (∑ p, (partitionUnitary X p).projector τ) - 1 ≠ 0 := sub_ne_zero.mpr hn
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting τ _ hz
  let : AddCommGroup S.toSubmodule := inferInstance
  let : Module ℂ S.toSubmodule := inferInstance
  have : S.toRepresentation.IsIrreducible := hS
  obtain ⟨p,⟨ep⟩⟩ := partitionUnitary_complete X S.toRepresentation
  have hval (q) (w : Fin (partitionUnitary X p).dimension → ℂ) :
      ((partitionUnitary X q).projector τ) (ep w : V)=
        if q=p then (ep w : V) else 0 := by
    have hh := (partitionUnitary X q).projector_intertwiner
      (partitionUnitary X p).asRepresentation S.toRepresentation ep.toIntertwiningMap w
    have hincl : ∀ u : S.toSubmodule,
        (((partitionUnitary X q).projector S.toRepresentation) u : V)=
          ((partitionUnitary X q).projector τ) (u : V) := by
      intro u
      simp [UnitaryIrrep.projector,Subrepresentation.toRepresentation]
    rw [← hincl]
    have hh' : ((partitionUnitary X q).projector S.toRepresentation) (ep w)=
        ep (((partitionUnitary X q).projector (partitionUnitary X p).asRepresentation) w) := by
      exact hh
    rw [hh',UnitaryIrrep.projector_matrix_asRepresentation]
    split_ifs with he
    · subst q
      rw [UnitaryIrrep.projector_self,map_one]
      rfl
    · rw [UnitaryIrrep.projector_other _ _ (partitionUnitary_inequivalent X q p he),map_zero]
      simp
  have hs : (∑ q, (partitionUnitary X q).projector τ) (v : V)=(v : V) := by
    obtain ⟨w,rfl⟩ := ep.surjective v
    rw [LinearMap.sum_apply]
    calc
      _ = ∑ q, (if q=p then (ep w : V) else 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hval q w
      _ = _ := by simp
  exact hv (by simp only [LinearMap.sub_apply,Module.End.one_apply,hs,sub_self])

end CoordinateSweeps.YoungCorner
namespace CoordinateSweeps.YoungCorner
variable (X : Type) [Fintype X] [DecidableEq X]
lemma partition_matrix_resolution {J : Type} [Fintype J] [DecidableEq J]
    (τ : Equiv.Perm X →* Matrix J J ℂ) :
    ∑ p, (partitionUnitary X p).projector τ=1 := by
  apply Matrix.toLinAlgEquiv'.injective
  have hh := partition_projector_resolution X (UnitaryIrrep.matrixRepresentation τ)
  have hm (p : Nat.Partition (Fintype.card X)) :
      Matrix.toLinAlgEquiv' ((partitionUnitary X p).projector τ)=
        (partitionUnitary X p).projector (UnitaryIrrep.matrixRepresentation τ) := by
    simp only [UnitaryIrrep.projector,map_sum,map_smul]
    rfl
  rw [map_sum,map_one]
  simpa only [hm] using hh

end CoordinateSweeps.YoungCorner

end
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
-- module Solutions.OAIQ56_CS.SignedTensor_Resolution
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
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.SignedTensor

lemma activeProjector_nonzero {p l : ℕ} (a : ActiveType p l) :
    (activeProjector a).val ≠ 0 := a.property

lemma active_inequivalent {p l : ℕ} (a b : ActiveType p l) (hab : a ≠ b) :
    ¬Nonempty (Representation.Equiv (activeIrrep a).asRepresentation (activeIrrep b).asRepresentation) := by
  apply YoungCorner.partitionUnitary_inequivalent
  intro h
  apply hab
  apply Subtype.ext
  simpa using h

lemma activeProjector_mul {p l : ℕ} (a b : ActiveType p l) :
    (activeProjector a).val*(activeProjector b).val=
      if a=b then (activeProjector a).val else 0 := by
  split_ifs with h
  · subst b; exact (activeIrrep a).projector_idempotent _
  · exact (activeIrrep a).projector_orthogonal (activeIrrep b)
      (active_inequivalent b a (Ne.symm h)) _

lemma activeProjector_independent (p l : ℕ) :
    LinearIndependent ℂ (activeProjector (p := p) (l := l)) := by
  apply linearIndependent_iff'.mpr
  intro t c hc a ha
  have hh := congrArg (fun A : commutant p l => (activeProjector a).val*A.val) hc
  have hv : ∑ b ∈ t, c b • ((activeProjector a).val*(activeProjector b).val)=0 := by
    simpa only [Submodule.coe_sum,Submodule.coe_smul,ZeroMemClass.coe_zero,
      Matrix.mul_sum,Matrix.mul_smul,mul_zero] using hh
  simp only [activeProjector_mul,smul_ite,smul_zero] at hv
  have he : c a • (activeProjector a).val=0 := by simpa [ha] using hv
  exact (smul_eq_zero.mp he).resolve_right (activeProjector_nonzero a)

/- Number of actually occurring local types is polynomial even without a
hook-support classification; this is exactly the term-count scale in06:eq20. -/
theorem active_card_le (p l : ℕ) :
    Fintype.card (ActiveType p l) ≤ (l+1)^((2*p)*(2*p)) :=
  (activeProjector_independent p l).fintype_card_le_finrank.trans (commutant_finrank_le p l)

/- Omitting zero type projections preserves the actual identity resolution. -/
theorem active_resolution (p l : ℕ) :
    ∑ a : ActiveType p l, (activeProjector a).val=1 := by
  let f (a : Nat.Partition (Fintype.card (Fin l))) :=
    (YoungCorner.partitionUnitary (Fin l) a).projector (action p l)
  have he : ∑ a : ActiveType p l, (activeProjector a).val=∑ a : Nat.Partition (Fintype.card (Fin l)), f a := by
    change (∑ a : {a : Nat.Partition (Fintype.card (Fin l)) // f a ≠ 0}, f a.val)=∑ a, f a
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a => f a ≠ 0)) (by simp),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp h).symm
  rw [he]
  have hh := YoungCorner.partition_matrix_resolution (Fin l) (action p l)
  simpa [f] using hh

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} (n : Fin r → ℕ)
lemma block_resolution : ∑ α : BlockType n p, blockProjector n α=1 := by
  simp only [blockProjector,groupedProjector_factor]
  change (∑ α : BlockType n p, Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm
    (DependentTensor.tensor (fun i => (activeIrrep (α i)).projector (action p (n i)))))=1
  rw [← map_sum]
  rw [← DependentTensor.tensor_sum (fun i (a : ActiveType p (n i)) => (activeIrrep a).projector (action p (n i)))]
  have hh (i : Fin r) : ∑ a : ActiveType p (n i), (activeIrrep a).projector (action p (n i))=1 :=
    active_resolution p (n i)
  simp only [hh,DependentTensor.tensor_one,map_one]

lemma block_card_le (s : ℕ) (hn : ∀ i, n i ≤ s) :
    Fintype.card (BlockType n p) ≤ (s+1)^(r*((2*p)*(2*p))) := by
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ i : Fin r, (s+1)^((2*p)*(2*p)) := Finset.prod_le_prod' (fun i hi =>
      (active_card_le p (n i)).trans (Nat.pow_le_pow_left (Nat.succ_le_succ (hn i)) _))
    _ = _ := by rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul,Nat.mul_comm]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open UnitaryIrrep FiberBlocks
variable {p r l : ℕ} (n : Fin r → ℕ)
lemma ambient_block_resolution (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l)) :
    (∑ α : BlockType n p, ambientProjector (p := p) n h σ (fun i => activeIrrep (α i)))=1 := by
  subst l
  unfold ambientProjector lengthMatrix
  rw [← Matrix.sum_mul,← Matrix.mul_sum,block_resolution,mul_one,matrix_unitary_reverse]

variable {L : Type*} [Fintype L]
lemma fiber_block_resolution (f : L → Fin r) (e : Fin (Fintype.card L) ≃ L) :
    (∑ α : BlockType (size f) p, fiberProjector (p := p) f e (fun i => activeIrrep (α i)))=1 :=
  ambient_block_resolution _ _ _

lemma exp_blockEntropy {n : Fin r → ℕ} (α : BlockType n p) :
    Real.exp (blockEntropy α)=∏ i, ((activeIrrep (α i)).dimension : ℝ) := by
  rw [blockEntropy,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (Nat.cast_pos.mpr (activeIrrep (α i)).positive)

lemma nat_pow_eq_exp (s t : ℕ) : ((s+1 : ℕ) : ℝ)^t=Real.exp ((t : ℝ)*Real.log (s+1 : ℕ)) := by
  rw [mul_comm,Real.exp_mul,Real.exp_log (by positivity),Real.rpow_natCast]

lemma block_card_real_le (f : L → Fin r) (s : ℕ) (hn : ∀ i, size f i ≤ s) :
    (Fintype.card (BlockType (size f) p) : ℝ) ≤
      Real.exp ((r*((2*p)*(2*p)) : ℕ)*Real.log (s+1 : ℕ)) := by
  rw [← nat_pow_eq_exp]
  exact_mod_cast block_card_le (size f) s hn

lemma actual_label_overlap_exp {c : ℕ} [NeZero r]
    (f : L → Fin r) (g : L → Fin c) (hinj : Function.Injective (fun x => (f x,g x)))
    (e : Fin (Fintype.card L) ≃ L) (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hnR : ∀ i, size f i ≤ s) (hnC : ∀ j, size g j ≤ s)
    (α : BlockType (size f) p) (β : BlockType (size g) p)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) :
    ‖fiberProjector g e (fun j => activeIrrep (β j))*ρ.projector (action p (Fintype.card L))*
      fiberProjector f e (fun i => activeIrrep (α i))‖^2 ≤
        Real.exp (blockEntropy α+blockEntropy β-Real.log ρ.dimension+
          ((r : ℝ)*c-Fintype.card L)+((r+c)*(41*p^2) : ℕ)*Real.log (s+1 : ℕ)) := by
  have hh := actual_label_overlap f g hinj e s hp hps hnR hnC
    (fun i => activeIrrep (α i)) (fun j => activeIrrep (β j)) ρ
  have hD : 0 < (ρ.dimension : ℝ) := Nat.cast_pos.mpr ρ.positive
  apply (mul_le_mul_iff_right₀ hD).mp
  apply hh.trans_eq
  rw [← exp_blockEntropy α,← exp_blockEntropy β,nat_pow_eq_exp,nat_pow_eq_exp]
  nth_rw 1 [← Real.exp_log hD]
  simp only [← Real.exp_add]
  congr 1
  push_cast
  ring

lemma actual_label_overlap_contract {c : ℕ} (f : L → Fin r) (g : L → Fin c)
    (e : Fin (Fintype.card L) ≃ L) (hp : 0 < p)
    (α : BlockType (size f) p) (β : BlockType (size g) p)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) :
    ‖fiberProjector g e (fun j => activeIrrep (β j))*ρ.projector (action p (Fintype.card L))*
      fiberProjector f e (fun i => activeIrrep (α i))‖ ≤ 1 := by
  let : NeZero (2*p) := ⟨by omega⟩
  have hR := TraceHolder.projector_norm_le _ (fiberProjector_posSemidef f e _).isHermitian
    (fiberProjector_idempotent (p := p) f e (fun i => activeIrrep (α i)))
  have hC := TraceHolder.projector_norm_le _ (fiberProjector_posSemidef g e _).isHermitian
    (fiberProjector_idempotent (p := p) g e (fun i => activeIrrep (β i)))
  have hP := TraceHolder.projector_norm_le _ (ρ.projector_posSemidef _ (fun σ => (matrix_inv σ).symm)).isHermitian
    (ρ.projector_idempotent (action p (Fintype.card L)))
  calc
    _ ≤ (‖fiberProjector g e (fun j => activeIrrep (β j))‖*‖ρ.projector (action p (Fintype.card L))‖)*
      ‖fiberProjector f e (fun i => activeIrrep (α i))‖ := by
        exact (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*1)*1 := mul_le_mul (mul_le_mul hC hP (norm_nonneg _) (by positivity)) hR
      (norm_nonneg _) (by positivity)
    _ = 1 := by norm_num

/- The actual two-product-subgroup inequality. Its only analytic inputs are
child moments; the resolution, polynomial number of types and board overlap
are all constructed above. This is the row/column step of the main induction. -/
theorem labeled_projected_moment_bound {c : ℕ} [NeZero r]
    (f : L → Fin r) (g : L → Fin c) (hinj : Function.Injective (fun x => (f x,g x)))
    (e : Fin (Fintype.card L) ≃ L) (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hnR : ∀ i, size f i ≤ s) (hnC : ∀ j, size g j ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) (q : ℕ) (hq : 0 < q)
    (c₀ ER EC : ℝ) (hc : 0 ≤ c₀) (hcq : c₀ ≤ q)
    (X Y : Matrix (Word p (Fintype.card L)) (Word p (Fintype.card L)) ℂ)
    (hR : ∀ α : BlockType (size f) p,
      (Matrix.trace (((fiberProjector f e (fun i => activeIrrep (α i))*X).conjTranspose*
        (fiberProjector f e (fun i => activeIrrep (α i))*X))^q)).re ≤ Real.exp (-c₀*blockEntropy α+ER))
    (hC : ∀ β : BlockType (size g) p,
      (Matrix.trace (((Y*fiberProjector g e (fun j => activeIrrep (β j))).conjTranspose*
        (Y*fiberProjector g e (fun j => activeIrrep (β j))))^q)).re ≤ Real.exp (-c₀*blockEntropy β+EC)) :
    (Matrix.trace (((Y*ρ.projector (action p (Fintype.card L))*X).conjTranspose*
      (Y*ρ.projector (action p (Fintype.card L))*X))^q)).re ≤
      Real.exp (-c₀*Real.log ρ.dimension+ER+EC+c₀*((r : ℝ)*c-Fintype.card L)+
        ((2*q : ℕ)*((r+c)*((2*p)*(2*p)) : ℕ)+c₀*((r+c)*(41*p^2) : ℕ))*Real.log (s+1 : ℕ)) := by
  let : NeZero (2*p) := ⟨by omega⟩
  have hh := TraceHolder.row_column_moment q hq
    (fun α : BlockType (size f) p => fiberProjector f e (fun i => activeIrrep (α i)))
    (fun β : BlockType (size g) p => fiberProjector g e (fun j => activeIrrep (β j)))
    (fiber_block_resolution f e) (fiber_block_resolution g e)
    (fun α => fiberProjector_idempotent f e _) (fun β => fiberProjector_idempotent g e _)
    (ρ.projector (action p (Fintype.card L))) X Y blockEntropy blockEntropy (Real.log ρ.dimension)
    (ER+EC) (((r : ℝ)*c-Fintype.card L)+((r+c)*(41*p^2) : ℕ)*Real.log (s+1 : ℕ)) c₀ hc hcq
    (fun α β => (mul_le_mul (hR α) (hC β)
      (by exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _ |>.pow q |>.trace_nonneg)).1)
      (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; congr 1; ring))
    (fun α β => by simpa only [add_assoc] using actual_label_overlap_exp f g hinj e s hp hps hnR hnC α β ρ)
    (fun α β => actual_label_overlap_contract f g e hp α β ρ)
  apply hh.trans
  have hcard := mul_le_mul (block_card_real_le (p := p) f s hnR) (block_card_real_le (p := p) g s hnC)
    (Nat.cast_nonneg _) (Real.exp_pos _).le
  rw [← Real.exp_add] at hcard
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤
    (Fintype.card (BlockType (size f) p) : ℝ)*(Fintype.card (BlockType (size g) p) : ℝ)) hcard (2*q)
  rw [← Real.exp_nat_mul] at hpow
  rw [Nat.cast_mul]
  apply (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
lemma phase_eq_of_same_parity {p l : ℕ} (σ : Equiv.Perm (Fin l)) (u w : Word p l)
    (h : ∀ i, odd (u i) ↔ odd (w i)) : phase σ u=phase σ w := by
  rw [phase_prod,phase_prod]
  apply Finset.prod_congr rfl
  intro ij hij
  simp only [h]

lemma wordPerm_same_parity {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, odd (w (σ i)) ↔ odd (w i)) :
    ∀ i, odd (wordPerm σ w i) ↔ odd (w i) := by
  intro i
  simpa [wordPerm] using (h (σ⁻¹ i)).symm

lemma phase_conj_of_parity_stable {p l : ℕ} (σ g : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, odd (w (σ i)) ↔ odd (w i)) :
    phase (g*σ*g⁻¹) (wordPerm g w)=phase σ w := by
  have he : (g*σ*g⁻¹)*g=g*σ := by simp [mul_assoc]
  have hh := phase_mul (g*σ*g⁻¹) g w
  rw [he,phase_mul,phase_eq_of_same_parity g _ w (wordPerm_same_parity σ w h)] at hh
  apply mul_right_cancel₀ (phase_ne_zero g w)
  rw [← hh,mul_comm]

lemma phase_of_fix_odd {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, odd (w i) → σ i=i) : phase σ w=1 := by
  rw [phase_prod]
  apply Finset.prod_eq_one
  intro ij hij
  have hj := Equiv.Perm.mem_finPairsLT.mp hij
  split_ifs with hh
  · rw [h _ hh.1,h _ hh.2.1] at hh
    exact False.elim (hj.not_gt hh.2.2)
  · rfl

lemma phase_swap_odd {p l : ℕ} (w : Word p l) (i j : Fin l) (hij : i ≠ j)
    (hi : odd (w i)) (hj : odd (w j)) : phase (Equiv.swap i j) w = -1 := by
  have hl : 2 ≤ l := by
    have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    omega
  obtain ⟨n,rfl⟩ : ∃ n, l=n+2 := ⟨l-2,by omega⟩
  obtain ⟨g,hgi,hgj⟩ := exists_perm_pair i j (0 : Fin (n+2)) 1 hij (by simp)
  have hp : ∀ x, odd (w (Equiv.swap i j x)) ↔ odd (w x) := by
    intro x
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have he : g*Equiv.swap i j*g⁻¹=Equiv.swap (0 : Fin (n+2)) 1 := by
    rw [Equiv.mul_swap_eq_swap_mul,mul_assoc,mul_inv_cancel,mul_one,hgi,hgj]
  have hh:=phase_conj_of_parity_stable (Equiv.swap i j) g w hp
  rw [he,phase_swap01] at hh
  have h0 : wordPerm g w 0=w i := by rw [← hgi]; simp [wordPerm]
  have h1 : wordPerm g w 1=w j := by rw [← hgj]; simp [wordPerm]
  simpa [h0,h1,hi,hj] using hh.symm

lemma phase_ofSubtype {p l : ℕ} (w : Word p l)
    (σ : Equiv.Perm {i : Fin l // odd (w i)}) :
    phase (Equiv.Perm.ofSubtype σ) w = YoungCorner.signScalar σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp [phase_one]
  | swap_mul σ i j hij ih =>
    rw [map_mul,phase_mul,Equiv.Perm.ofSubtype_swap_eq]
    have hp := wordPerm_same_parity (Equiv.Perm.ofSubtype σ) w
      (Equiv.Perm.ofSubtype_apply_mem_iff_mem σ)
    rw [phase_eq_of_same_parity _ _ w hp,
      phase_swap_odd w i j (fun he => hij (Subtype.ext he)) i.property j.property,
      ih,map_mul,YoungCorner.signScalar_swap i j hij]

lemma phase_of_fix_even {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, ¬ odd (w i) → σ i=i) : phase σ w=YoungCorner.signScalar σ := by
  have hp : ∀ i, odd (w (σ i)) ↔ odd (w i) := by
    intro i
    by_cases hi : odd (w i)
    · have hs : odd (w (σ i)) := by
        by_contra hn
        have hh := h (σ i) hn
        have he := σ.injective hh
        rw [he] at hn
        exact hn hi
      simp [hi,hs]
    · rw [h i hi]
  let υ := Equiv.Perm.subtypePerm (p := fun i => odd (w i)) σ hp
  have he : Equiv.Perm.ofSubtype υ=σ := Equiv.Perm.ofSubtype_subtypePerm (p := fun i => odd (w i)) hp (by
    intro i hi
    exact Classical.byContradiction (fun hn => hi (h i hn)))
  rw [← he,phase_ofSubtype]
  simp [YoungCorner.signScalar,Equiv.Perm.sign_ofSubtype]

end CoordinateSweeps.SignedTensor
namespace CoordinateSweeps.YoungCorner
variable {μ : YoungDiagram} {p : ℕ}

lemma hookLetter_odd (h : Hook μ p) (x : Boxes μ) :
    SignedTensor.odd (hookLetter h x) ↔ p≤x.val.1 := by
  simp only [hookLetter,SignedTensor.odd]
  split_ifs <;> simp_all
  omega

lemma hookLetter_row_eq (h : Hook μ p) (x y : Boxes μ)
    (hx : x.val.1<p) (he : hookLetter h x=hookLetter h y) : x.val.1=y.val.1 := by
  have he' := congrArg Fin.val he
  simp only [hookLetter] at he'
  split_ifs at he' <;> simp_all
  omega

lemma hookLetter_col_eq (h : Hook μ p) (x y : Boxes μ)
    (hx : p≤x.val.1) (he : hookLetter h x=hookLetter h y) : x.val.2=y.val.2 := by
  have he' := congrArg Fin.val he
  simp only [hookLetter] at he'
  split_ifs at he' <;> simp_all <;> omega

/- The geometric reason all diagonal Young-corner coefficients have positive
sign on the actual even-row/odd-column hook word. -/
lemma hook_corner_fixed {X : Type*} (t : X ≃ Boxes μ) (h : Hook μ p)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t))
    (hw : ∀ x, hookLetter h (t ((r : Equiv.Perm X) (c.val x)))=hookLetter h (t x)) :
    (∀ x, (t x).val.1<p → c.val x=x) ∧ (∀ x, p≤(t x).val.1 → r.val x=x) := by
  have hc : ∀ x, (t x).val.1<p → c.val x=x := by
    intro x hx
    apply t.injective
    apply Subtype.ext
    apply Prod.ext
    · have hr:=r.property (c.val x)
      have hh:=hookLetter_row_eq h (t x) (t (r.val (c.val x))) hx (hw x).symm
      exact hr.symm.trans hh.symm
    · exact c.property x
  refine ⟨hc,?_⟩
  intro y hy
  let x := (c : Equiv.Perm X)⁻¹ y
  have hxy : c.val x=y := by simp [x]
  have hx : p≤(t x).val.1 := by
    by_contra hn
    have he := hc x (by omega)
    rw [hxy] at he
    rw [← he] at hn
    omega
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact r.property y
  · have hh:=hookLetter_col_eq h (t x) (t (r.val (c.val x))) hx (hw x).symm
    have hh' :=c.property x
    change (t (c.val x)).val.2=(t x).val.2 at hh'
    rw [hxy] at hh hh'
    exact hh.symm.trans hh'.symm

lemma hook_corner_phase {l : ℕ} (t : Fin l ≃ Boxes μ) (h : Hook μ p)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t))
    (hw : ∀ x, hookLetter h (t ((r : Equiv.Perm (Fin l)) (c.val x)))=hookLetter h (t x)) :
    SignedTensor.phase ((r : Equiv.Perm (Fin l))*c.val) (fun x => hookLetter h (t x))=
      signScalar (c : Equiv.Perm (Fin l)) := by
  obtain ⟨hc,hr⟩ := hook_corner_fixed t h r c hw
  let w : SignedTensor.Word p l := fun x => hookLetter h (t x)
  have hce : ∀ i, ¬ SignedTensor.odd (w i) → (c : Equiv.Perm (Fin l)) i=i := by
    intro i hi
    exact hc i (by simpa only [w,hookLetter_odd,not_le] using hi)
  have hcp : ∀ i, SignedTensor.odd (w (c.val i)) ↔ SignedTensor.odd (w i) := by
    intro i
    by_cases hi : SignedTensor.odd (w i)
    · have hh : SignedTensor.odd (w (c.val i)) := by
        by_contra hn
        have he := c.val.injective (hce (c.val i) hn)
        rw [he] at hn
        exact hn hi
      simp [hi,hh]
    · rw [hce i hi]
  rw [SignedTensor.phase_mul,SignedTensor.phase_eq_of_same_parity _ _ w
    (SignedTensor.wordPerm_same_parity c.val w hcp),SignedTensor.phase_of_fix_odd _ w]
  · rw [one_mul,SignedTensor.phase_of_fix_even c.val w hce]
  · intro i hi
    exact hr i ((hookLetter_odd h (t i)).mp hi)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {μ : YoungDiagram} {p l : ℕ}

lemma signScalar_square {X : Type*} [Fintype X] [DecidableEq X] (c : Equiv.Perm X) :
    signScalar c * signScalar c=1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h|h <;> simp [signScalar,h]

lemma hook_contribution (t : Fin l ≃ Boxes μ) (h : Hook μ p)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t)) :
    let w : SignedTensor.Word p l := fun x => hookLetter h (t x)
    signScalar c.val * SignedTensor.matrix (r.val*c.val) w w =
      if w=SignedTensor.wordPerm (r.val*c.val) w then 1 else 0 := by
  dsimp only
  rw [SignedTensor.matrix]
  split_ifs with he
  · have hw : ∀ x, hookLetter h (t (r.val (c.val x)))=hookLetter h (t x) := by
      intro x
      have hh := congrFun he ((r.val*c.val) x)
      simpa [SignedTensor.wordPerm,Equiv.Perm.mul_apply] using hh
    rw [hook_corner_phase t h r c hw,signScalar_square]
  · simp

lemma hook_corner_matrix_ne (t : Fin l ≃ Boxes μ) (h : Hook μ p) :
    fixedSum (rowColor t) (SignedTensor.action p l) *
      alternatingSum (colColor t) (SignedTensor.action p l) ≠ 0 := by
  let w : SignedTensor.Word p l := fun x => hookLetter h (t x)
  have he : (fixedSum (rowColor t) (SignedTensor.action p l) *
      alternatingSum (colColor t) (SignedTensor.action p l)) w w =
      ∑ r : colorStabilizer (rowColor t), ∑ c : colorStabilizer (colColor t),
        if w=SignedTensor.wordPerm (r.val*c.val) w then (1 : ℂ) else 0 := by
    rw [fixedSum,alternatingSum,Finset.sum_mul]
    simp only [Finset.mul_sum,mul_smul_comm,← map_mul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro c hc
    exact hook_contribution t h r c
  have hpos : 0 < ((fixedSum (rowColor t) (SignedTensor.action p l) *
      alternatingSum (colColor t) (SignedTensor.action p l)) w w).re := by
    rw [he]
    simp only [Complex.re_sum,apply_ite,Complex.one_re,Complex.zero_re]
    apply Finset.sum_pos'
    · intro r hr
      apply Finset.sum_nonneg
      intro c hc
      split_ifs <;> norm_num
    · refine ⟨1,Finset.mem_univ _,?_⟩
      apply Finset.sum_pos'
      · intro c hc
        split_ifs <;> norm_num
      · refine ⟨1,Finset.mem_univ _,?_⟩
        simp [SignedTensor.wordPerm]
  intro hz
  rw [hz] at hpos
  simp at hpos

/- The literal signed action, as a linear representation. -/

lemma signedRep_hasShape (t : Fin l ≃ Boxes μ) (h : Hook μ p) :
    hasShape μ t (signedRep p l) := by
  have he : fixedSum (rowColor t) (signedRep p l) * alternatingSum (colColor t) (signedRep p l) =
      Matrix.toLinAlgEquiv' (fixedSum (rowColor t) (SignedTensor.action p l) *
        alternatingSum (colColor t) (SignedTensor.action p l)) := by
    simp [fixedSum,alternatingSum,signedRep,map_sum,map_mul]
  intro hz
  rw [he] at hz
  exact hook_corner_matrix_ne t h (Matrix.toLinAlgEquiv'.injective (hz.trans (map_zero _).symm))

lemma detecting_shape_constituent {X V : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ (Equiv.Perm X) V) (t : X ≃ Boxes μ) (h : hasShape μ t τ) :
    ∃ S : Subrepresentation τ, S.toRepresentation.IsIrreducible ∧ hasShape μ t S.toRepresentation := by
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting τ
    (fixedSum (rowColor t) τ*alternatingSum (colColor t) τ) h
  refine ⟨S,hS,?_⟩
  intro hh
  apply hv
  have hz := congrArg (fun A : Module.End ℂ S.toSubmodule => (A v : V)) hh
  simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hz
  exact hz

/- Source05 hook occurrence, derived for actual irreps in the exact Koszul
representation. No Pieri/Schur--Weyl or hook classification is assumed. -/
theorem hook_occurs {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin l)) V) [ρ.IsIrreducible]
    (t : Fin l ≃ Boxes μ) (hρ : hasShape μ t ρ) (h : Hook μ p) :
    ∃ S : Subrepresentation (signedRep p l),
      Nonempty (Representation.Equiv ρ S.toRepresentation) := by
  obtain ⟨S,hS,hSh⟩ := detecting_shape_constituent (signedRep p l) t (signedRep_hasShape t h)
  let := hS
  exact ⟨S,equiv_of_same_shape ρ S.toRepresentation μ t t hρ hSh⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
open UnitaryIrrep SignedTensor
lemma hook_multiplicity_pos {p l : ℕ} {μ : YoungDiagram}
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) (t : Fin l ≃ Boxes μ)
    (hρ : hasShape μ t ρ.asRepresentation) (hhook : Hook μ p) :
    0 < Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation (action p l))) := by
  obtain ⟨S,⟨e⟩⟩ := hook_occurs ρ.asRepresentation t hρ hhook
  let inc : S.toRepresentation.IntertwiningMap (signedRep p l) :=
    ⟨S.toSubmodule.subtype,fun _ => rfl⟩
  let f := inc.comp e.toIntertwiningMap
  have hf : f ≠ 0 := by
    intro hz
    have hzero : ∀ v : Fin ρ.dimension → ℂ, v=0 := by
      intro v
      apply e.toLinearEquiv.injective
      apply Subtype.val_injective
      have hh := congrArg (fun g : ρ.asRepresentation.IntertwiningMap (signedRep p l) => g v) hz
      change ((e.toLinearEquiv v : S.toSubmodule) : SignedTensor.Word p l → ℂ)=0 at hh
      rw [map_zero]
      exact hh
    have : Nonempty (Fin ρ.dimension) := Fin.pos_iff_nonempty.mp ρ.positive
    exact one_ne_zero (congrFun (hzero (fun _ => 1)) (Classical.arbitrary (Fin ρ.dimension)))
  let : Nontrivial (ρ.asRepresentation.IntertwiningMap (signedRep p l)) := nontrivial_of_ne f 0 hf
  change 0 < Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (signedRep p l))
  exact Module.finrank_pos
end CoordinateSweeps.YoungCorner
end
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
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Induction
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
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma lineCount_row (j : Fin A.b) (L : A.Line j) (y : B.Slot) :
    H.lineCount (Fin.castAdd B.b j) (rowLines A B j (L,y))=(H.rowHoles y).lineCount j L := by
  exact (H.card_onLine _ _).symm.trans ((Fintype.card_congr (H.rowOnLineEquiv j L y)).symm.trans
    ((H.rowHoles y).card_onLine j L))
lemma lineCount_column (j : Fin B.b) (x : A.Slot) (L : B.Line j) :
    H.lineCount (Fin.natAdd A.b j) (columnLines A B j (x,L))=(H.columnHoles x).lineCount j L := by
  exact (H.card_onLine _ _).symm.trans ((Fintype.card_congr (H.columnOnLineEquiv j x L)).symm.trans
    ((H.columnHoles x).card_onLine j L))

/- One head stage contributes exactly the sum of its child row potentials. -/
lemma cost_stage_row (j : Fin A.b) :
    (∑ L : (concat A B).Line (Fin.castAdd B.b j),
      Real.log (((2 ^ (concat A B).bits (Fin.castAdd B.b j) : ℕ) : ℝ) ^
          H.lineCount (Fin.castAdd B.b j) L /
        ((2 ^ (concat A B).bits (Fin.castAdd B.b j)).descFactorial
          (H.lineCount (Fin.castAdd B.b j) L) : ℝ)))=
      ∑ y : B.Slot, ∑ L : A.Line j,
        Real.log (((2^A.bits j : ℕ) : ℝ)^(H.rowHoles y).lineCount j L /
          ((2^A.bits j).descFactorial ((H.rowHoles y).lineCount j L) : ℝ)) := by
  rw [← (rowLines A B j).sum_comp,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro L _
  rw [H.lineCount_row,concat_bits_left]

lemma cost_stage_column (j : Fin B.b) :
    (∑ L : (concat A B).Line (Fin.natAdd A.b j),
      Real.log (((2 ^ (concat A B).bits (Fin.natAdd A.b j) : ℕ) : ℝ) ^
          H.lineCount (Fin.natAdd A.b j) L /
        ((2 ^ (concat A B).bits (Fin.natAdd A.b j)).descFactorial
          (H.lineCount (Fin.natAdd A.b j) L) : ℝ)))=
      ∑ x : A.Slot, ∑ L : B.Line j,
        Real.log (((2^B.bits j : ℕ) : ℝ)^(H.columnHoles x).lineCount j L /
          ((2^B.bits j).descFactorial ((H.columnHoles x).lineCount j L) : ℝ)) := by
  rw [← (columnLines A B j).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro L _
  rw [H.lineCount_column,concat_bits_right]

/- No conditioning cost is discarded in the induction split. -/
theorem cost_split : H.cost=(∑ y, (H.rowHoles y).cost)+(∑ x, (H.columnHoles x).cost) := by
  unfold cost
  erw [Fin.sum_univ_add]
  congr 1
  · trans ∑ j : Fin A.b, ∑ y : B.Slot, ∑ L : A.Line j,
      Real.log (((2^A.bits j : ℕ) : ℝ)^(H.rowHoles y).lineCount j L /
        ((2^A.bits j).descFactorial ((H.rowHoles y).lineCount j L) : ℝ))
    · apply Finset.sum_congr rfl
      intro j _
      convert H.cost_stage_row j using 1
      all_goals try with_reducible_and_instances rfl
      congr 3
      exact Subsingleton.elim _ _
    · exact Finset.sum_comm
  · trans ∑ j : Fin B.b, ∑ x : A.Slot, ∑ L : B.Line j,
      Real.log (((2^B.bits j : ℕ) : ℝ)^(H.columnHoles x).lineCount j L /
        ((2^B.bits j).descFactorial ((H.columnHoles x).lineCount j L) : ℝ))
    · apply Finset.sum_congr rfl
      intro j _
      convert H.cost_stage_column j using 1
      all_goals try with_reducible_and_instances rfl
      congr 3
      exact Subsingleton.elim _ _
    · exact Finset.sum_comm

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks SignedTensor UnitaryIrrep
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma row_column_index_injective : Function.Injective (fun x : H.JunctionFree => (H.rowIndex x,H.columnIndex x)) := by
  intro x y he
  apply Subtype.ext
  apply (splitSlots A B).injective
  exact Prod.ext ((Fintype.equivFin A.Slot).injective (congrArg Prod.snd he))
    ((Fintype.equivFin B.Slot).injective (congrArg Prod.fst he))

lemma row_entropy_sum {p : ℕ} (α : BlockType (FiberBlocks.size H.rowIndex) p) (c e : ℝ) :
    (∑ i, (-c*Real.log (activeIrrep (α i)).dimension+
      e*H.rowCount (H.rowSite i)*Real.log A.size-(H.rowHoles (H.rowSite i)).cost))=
      -c*blockEntropy α+e*h*Real.log A.size-∑ y, (H.rowHoles y).cost := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    blockEntropy]
  have hc : (∑ i, (H.rowCount (H.rowSite i) : ℝ))=h := by
    rw [← Nat.cast_sum]
    congr 1
    exact ((Fintype.equivFin B.Slot).symm.sum_comp H.rowCount).trans H.sum_rowCount
  rw [hc]
  congr 1
  exact (Fintype.equivFin B.Slot).symm.sum_comp (fun y => (H.rowHoles y).cost)

lemma column_entropy_sum {p : ℕ} (β : BlockType (FiberBlocks.size H.columnIndex) p) (c e : ℝ) :
    (∑ i, (-c*Real.log (activeIrrep (β i)).dimension+
      e*H.columnCount (H.columnSite i)*Real.log B.size-(H.columnHoles (H.columnSite i)).cost))=
      -c*blockEntropy β+e*h*Real.log B.size-∑ x, (H.columnHoles x).cost := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    blockEntropy]
  have hc : (∑ i, (H.columnCount (H.columnSite i) : ℝ))=h := by
    rw [← Nat.cast_sum]
    congr 1
    exact ((Fintype.equivFin A.Slot).symm.sum_comp H.columnCount).trans H.sum_columnCount
  rw [hc]
  congr 1
  exact (Fintype.equivFin A.Slot).symm.sum_comp (fun x => (H.columnHoles x).cost)

variable (p : ℕ) (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) (q : ℕ) (hq : 0 < q) (c e : ℝ) (s : ℕ)
theorem row_child_hook_bound (hq : 0 < q) (hAS : A.size ≤ s)
    (hR : ∀ y : B.Slot, ∀ σ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (α : BlockType (FiberBlocks.size H.rowIndex) p) :
      (Matrix.trace (((fiberProjector H.rowIndex eF (fun i => activeIrrep (α i))*
        H.rowAverage hf z (H.junctionTensorAction p eF)).conjTranspose*
        (fiberProjector H.rowIndex eF (fun i => activeIrrep (α i))*
        H.rowAverage hf z (H.junctionTensorAction p eF)))^q)).re ≤ Real.exp (-c*blockEntropy α+(e*h*Real.log A.size-(∑ y, (H.rowHoles y).cost)+
        ((B.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ))) := by
    have hh := H.row_moment_bound p eF hf z hq.ne' (fun i => activeIrrep (α i))
      (fun i => -c*Real.log (activeIrrep (α i)).dimension+
        e*H.rowCount (H.rowSite i)*Real.log A.size-(H.rowHoles (H.rowSite i)).cost)
      (fun i => hR (H.rowSite i) _)
    apply hh.trans
    have hn : ((A.size+1 : ℕ):ℝ)^(B.size*((2*p)*(2*p))) ≤
        ((s+1 : ℕ):ℝ)^(B.size*((2*p)*(2*p))) := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.add_le_add_right hAS 1) _
    apply (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le).trans_eq
    rw [nat_pow_eq_exp,H.row_entropy_sum,← Real.exp_add]
    congr 1
    ring
theorem column_child_hook_bound (hq : 0 < q) (hBS : B.size ≤ s)
    (hC : ∀ x : A.Slot, ∀ σ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost))
    (β : BlockType (FiberBlocks.size H.columnIndex) p) :
      (Matrix.trace (((H.columnAverage hf z (H.junctionTensorAction p eF)*
        fiberProjector H.columnIndex eF (fun i => activeIrrep (β i))).conjTranspose*
        (H.columnAverage hf z (H.junctionTensorAction p eF)*
        fiberProjector H.columnIndex eF (fun i => activeIrrep (β i))))^q)).re ≤ Real.exp (-c*blockEntropy β+(e*h*Real.log B.size-(∑ x, (H.columnHoles x).cost)+
        ((A.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ))) := by
    have hh := H.column_moment_bound p eF hf z hq.ne' (fun i => activeIrrep (β i))
      (fun i => -c*Real.log (activeIrrep (β i)).dimension+
        e*H.columnCount (H.columnSite i)*Real.log B.size-(H.columnHoles (H.columnSite i)).cost)
      (fun i => hC (H.columnSite i) _)
    apply hh.trans
    have hn : ((B.size+1 : ℕ):ℝ)^(A.size*((2*p)*(2*p))) ≤
        ((s+1 : ℕ):ℝ)^(A.size*((2*p)*(2*p))) := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.add_le_add_right hBS 1) _
    apply (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le).trans_eq
    rw [nat_pow_eq_exp,H.column_entropy_sum,← Real.exp_add]
    congr 1
    ring
/- Exact row/column induction estimate on the literal free junction board.
Only smaller-grid conditional estimates enter as hypotheses. -/
theorem grid_projected_hook_bound (p : ℕ) (hp : 0 < p)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (hf : H.Feasible)
    (z : ℝ) (q : ℕ) (hq : 0 < q) (c e : ℝ) (hc : 0 ≤ c) (hcq : c ≤ q)
    (s : ℕ) (hpS : p ≤ s) (hAS : A.size ≤ s) (hBS : B.size ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree))))
    (hR : ∀ y : B.Slot, ∀ σ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (hC : ∀ x : A.Slot, ∀ σ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost)) :
    let X := H.rowAverage hf z (H.junctionTensorAction p eF)
    let Y := H.columnAverage hf z (H.junctionTensorAction p eF)
    let P := ρ.projector (action p (Fintype.card H.JunctionFree))
    (Matrix.trace (((Y*P*X).conjTranspose*(Y*P*X))^q)).re ≤
      Real.exp (-c*Real.log ρ.dimension+e*h*(Real.log A.size+Real.log B.size)-H.cost+c*h+
        (((2*q+1 : ℕ) : ℝ)*((A.size+B.size)*((2*p)*(2*p)) : ℕ)+
          c*((A.size+B.size)*(41*p^2) : ℕ))*Real.log (s+1 : ℕ)) := by
  dsimp only
  let : NeZero (Fintype.card B.Slot) := ⟨Fintype.card_ne_zero⟩
  let ER := e*h*Real.log A.size-(∑ y, (H.rowHoles y).cost)+
    ((B.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ)
  let EC := e*h*Real.log B.size-(∑ x, (H.columnHoles x).cost)+
    ((A.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ)
  have hr := H.row_child_hook_bound (p := p) (eF := eF) (hf := hf) (z := z) (q := q) (c := c) (e := e) (s := s) hq hAS hR
  have hc' := H.column_child_hook_bound (p := p) (eF := eF) (hf := hf) (z := z) (q := q) (c := c) (e := e) (s := s) hq hBS hC
  have hh := labeled_projected_moment_bound H.rowIndex H.columnIndex H.row_column_index_injective eF s hp hpS
    (fun i => (H.row_size_le i).trans hAS) (fun i => (H.column_size_le i).trans hBS)
    ρ q hq c ER EC hc hcq (H.rowAverage hf z (H.junctionTensorAction p eF))
      (H.columnAverage hf z (H.junctionTensorAction p eF)) hr hc'
  apply hh.trans_eq
  congr 1
  dsimp [ER,EC]
  rw [H.cost_split]
  simp only [card_slot]
  -- Exact number of deleted junction sites, including h=s and empty fibers.
  have hm : ((B.size:ℝ)*A.size-Fintype.card H.JunctionFree)=(h:ℝ) := by
    rw [H.card_freeAt]
    have hh : h ≤ (concat A B).size := by
      simpa only [Fintype.card_fin,card_slot] using Fintype.card_le_of_injective (H.path · 0) (H.disjoint 0)
    rw [Nat.cast_sub hh]
    simp only [concat_size,Nat.cast_mul]
    ring
  rw [hm]
  push_cast
  ring
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep SignedTensor YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma junction_projector_commute_column (p : ℕ) (hf : H.Feasible)
    (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree)))) :
    ρ.projector (action p _) * H.columnAverage hf z (H.junctionTensorAction p e)=
      H.columnAverage hf z (H.junctionTensorAction p e) * ρ.projector (action p _) := by
  exact ρ.projector_commute_average (action p _)
    (fun ω : H.ColumnChoices => ((∏ x, B.choiceWeight z (ω x).val/(H.columnHoles x).probability z : ℝ) : ℂ))
    (fun ω => e.symm.permCongrHom (H.junctionFreeEquiv (H.columnResidual hf ω)))

/- The exact projected tensor moment on the literal junction board equals
its genuine Hom multiplicity times the main theorem's conditional moment. -/
theorem junction_projected_moment (p : ℕ) (hf : H.Feasible)
    (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree)))) {q : ℕ} (hq : q ≠ 0) :
    let X := H.rowAverage hf z (H.junctionTensorAction p e)
    let Y := H.columnAverage hf z (H.junctionTensorAction p e)
    let P := ρ.projector (action p (Fintype.card H.JunctionFree))
    (Matrix.trace (((Y*P*X).conjTranspose*(Y*P*X))^q)).re =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (Fintype.card H.JunctionFree)))) : ℝ) *
        schattenMoment q (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e))) := by
  dsimp only
  let w : {ω : (concat A B).Choices // H.Compatible ω} → ℂ := fun ω =>
    (((concat A B).choiceWeight z ω.val/H.probability z : ℝ) : ℂ)
  let g := fun ω => H.junctionChart hf e (H.residual hf ω)
  have ha : averageMatrix (action p (Fintype.card H.JunctionFree)) w g =
      H.columnAverage hf z (H.junctionTensorAction p e)*H.rowAverage hf z (H.junctionTensorAction p e) :=
    H.junction_average_split hf z (H.junctionTensorAction p e)
  have hb : averageMatrix ρ.matrix w g=H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e)) := by
    rw [H.conditionalAverage_eq_sum]
    rfl
  have he := ρ.projected_operator_moment (action p _) (fun σ => (matrix_inv σ).symm) w g hq
  have hc : ρ.projector (action p _)*averageMatrix (action p _) w g=
      H.columnAverage hf z (H.junctionTensorAction p e)*ρ.projector (action p _)*
        H.rowAverage hf z (H.junctionTensorAction p e) := by
    rw [ha,← mul_assoc,H.junction_projector_commute_column]
  rw [hc] at he
  have hre := congrArg Complex.re he
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hre
  calc
    _ = _ * schattenMoment q (averageMatrix ρ.matrix w g) := hre
    _ = _ := congrArg (fun M : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ =>
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (Fintype.card H.JunctionFree)))) : ℝ)*schattenMoment q M) hb

/- Hook occurrence removes the multiplicity without normalizing the trace. -/
theorem conditional_hook_moment_le_projected (p : ℕ) (hf : H.Feasible)
    (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree)))) {q : ℕ} (hq : q ≠ 0)
    (μ : YoungDiagram) (t : Fin (Fintype.card H.JunctionFree) ≃ Boxes μ)
    (hρ : hasShape μ t ρ.asRepresentation) (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e))) ≤
      (Matrix.trace (((H.columnAverage hf z (H.junctionTensorAction p e)*
        ρ.projector (action p _)*H.rowAverage hf z (H.junctionTensorAction p e)).conjTranspose*
        (H.columnAverage hf z (H.junctionTensorAction p e)*
        ρ.projector (action p _)*H.rowAverage hf z (H.junctionTensorAction p e)))^q)).re := by
  rw [H.junction_projected_moment p hf e z ρ hq]
  have hn := hook_multiplicity_pos ρ t hρ hhook
  have hr : (1 : ℝ) ≤ Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (action p (Fintype.card H.JunctionFree)))) := by exact_mod_cast hn
  have ht := trace_moment_nonneg (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e))) q
  exact (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right hr ht)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep SignedTensor YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
theorem grid_conditional_hook_bound (p : ℕ) (hp : 0 < p)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (hf : H.Feasible)
    (z : ℝ) (q : ℕ) (hq : 0 < q) (c e : ℝ) (hc : 0 ≤ c) (hcq : c ≤ q)
    (s : ℕ) (hpS : p ≤ s) (hAS : A.size ≤ s) (hBS : B.size ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree))))
    (hR : ∀ y : B.Slot, ∀ σ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (hC : ∀ x : A.Slot, ∀ σ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost))
    (μ : YoungDiagram) (t : Fin (Fintype.card H.JunctionFree) ≃ Boxes μ)
    (hρ : hasShape μ t ρ.asRepresentation) (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf eF))) ≤
      Real.exp (-c*Real.log ρ.dimension+e*h*(Real.log A.size+Real.log B.size)-H.cost+c*h+
        (((2*q+1 : ℕ) : ℝ)*((A.size+B.size)*((2*p)*(2*p)) : ℕ)+
          c*((A.size+B.size)*(41*p^2) : ℕ))*Real.log (s+1 : ℕ)) := by
  exact (H.conditional_hook_moment_le_projected p hf eF z ρ hq.ne' μ t hρ hhook).trans
    (H.grid_projected_hook_bound p hp eF hf z q hq c e hc hcq s hpS hAS hBS ρ hR hC)
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
-- module Solutions.OAIQ56_CS.Matrix_BlockCycles
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
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.BlockCycles
variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [Semiring R]

omit [DecidableEq Ω] in
lemma sum_tuple_split {S : Type*} [AddCommMonoid S] (n : ℕ) (f : (Fin (n+1) → Ω) → S) :
    ∑ x, f x=∑ a, ∑ x : Fin n → Ω, f (Fin.cons a x) := by
  rw [← Equiv.sum_comp (tupleSplit (Ω := Ω) n).symm]
  exact Fintype.sum_prod_type _

omit [Fintype Ω] [DecidableEq Ω] in
lemma walk_succ {n : ℕ} (A : Fin (n+1) → Matrix Ω Ω R) (x : Fin (n+2) → Ω) :
    walk A x=A 0 (x 0) (x 1)*walk (fun i => A i.succ) (fun i => x i.succ) := by
  rw [walk,List.ofFn_succ,List.prod_cons]
  rfl

omit [Fintype Ω] [DecidableEq Ω] in
lemma snoc_cons {n : ℕ} (x : Fin n → Ω) (i j : Ω) :
    Fin.snoc (α := fun _ => Ω) (Fin.cons i x) j=Fin.cons i (Fin.snoc (α := fun _ => Ω) x j) := by
  funext k
  refine Fin.lastCases ?_ (fun l => ?_) k
  · simp
  · cases l using Fin.cases with
    | zero => simp
    | succ l =>
        simp only [Fin.snoc_castSucc,Fin.cons_succ]
        rw [← Fin.succ_castSucc,Fin.cons_succ,Fin.snoc_castSucc]

/- Complete matrix product expansion by paths, with the endpoint checked rather
than divided out. Valid for any noncommutative semiring of blocks. -/
lemma product_entry {n : ℕ} (A : Fin n → Matrix Ω Ω R) (i j : Ω) :
    ((List.ofFn A).prod) i j=
      ∑ x : Fin n → Ω, if (Fin.snoc (α := fun _ => Ω) x j) 0=i then walk A (Fin.snoc (α := fun _ => Ω) x j) else 0 := by
  induction n generalizing i j with
  | zero =>
    simp [walk,Matrix.one_apply,Fin.snoc_zero,eq_comm]
  | succ n ih =>
    rw [List.ofFn_succ,List.prod_cons,Matrix.mul_apply,sum_tuple_split]
    have hr : (∑ u : Ω, ∑ x : Fin n → Ω,
        if (Fin.snoc (α := fun _ => Ω) (Fin.cons u x) j) 0=i then walk A (Fin.snoc (α := fun _ => Ω) (Fin.cons u x) j) else 0)=
          ∑ x : Fin n → Ω, walk A (Fin.snoc (α := fun _ => Ω) (Fin.cons i x) j) := by
      rw [Finset.sum_eq_single i]
      · simp only [snoc_cons,Fin.cons_zero,ite_true]
      · intro u _ hu
        simp [hu]
      · simp
    rw [hr]
    simp only [ih,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [snoc_cons,walk_succ]
    simp only [Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
    rw [Finset.sum_eq_single ((Fin.snoc (α := fun _ => Ω) x j) 0)]
    · simp
    · intro u _ hu
      simp [Ne.symm hu]
    · simp

omit [Fintype Ω] [DecidableEq Ω] in
lemma snoc_cycle {n : ℕ} (x : Fin (n+1) → Ω) (i : Fin (n+1)) :
    Fin.snoc (α := fun _ => Ω) x (x 0) i.succ=x (i+1) := by
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
    have he : i.castSucc+1=i.succ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (Fin.castSucc_lt_last i)
    rw [he]
    rw [Fin.succ_castSucc]
    exact Fin.snoc_castSucc (α := fun _ => Ω) (x 0) x i.succ

/- Exact cyclic trace expansion, also when entries themselves are matrices. -/
theorem trace_product {n : ℕ} (A : Fin (n+1) → Matrix Ω Ω R) :
    Matrix.trace ((List.ofFn A).prod)=
      ∑ x : Fin (n+1) → Ω, (List.ofFn (fun i => A i (x i) (x (i+1)))).prod := by
  unfold Matrix.trace Matrix.diag
  simp_rw [product_entry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (x 0)]
  · rw [show (Fin.snoc (α := fun _ => Ω) x (x 0)) 0=x 0 from Fin.snoc_castSucc (α := fun _ => Ω) (x 0) x (0 : Fin (n+1)),ite_eq_left rfl]
    unfold walk
    congr 2
    funext i
    rw [Fin.snoc_castSucc,snoc_cycle]
  · intro i _ hi
    have he : (Fin.snoc (α := fun _ => Ω) x i) 0=x 0 := by exact Fin.snoc_castSucc (α := fun _ => Ω) i x (0 : Fin (n+1))
    rw [he,ite_eq_right (Ne.symm hi)]
  · simp

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
variable {Ω n R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Semiring R]

lemma trace_blocks (A : Matrix (Ω × n) (Ω × n) R) :
    Matrix.trace A=Matrix.trace (Matrix.trace (blocks A)) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.sum_apply,blocks_apply]
  rw [Fintype.sum_prod_type,Finset.sum_comm]

/- Exact placement-cycle expansion of a product of operators on placement fibers. -/
theorem trace_block_product {m : ℕ} [NeZero m] (hm : 0 < m)
    (A : Fin m → Matrix (Ω × n) (Ω × n) R) :
    Matrix.trace (List.ofFn A).prod=
      ∑ x : Fin m → Ω, Matrix.trace (List.ofFn (fun i => blocks (A i) (x i) (x (i+1)))).prod := by
  cases m with
  | zero => omega
  | succ m =>
    rw [trace_blocks,map_list_prod]
    simp only [List.map_ofFn]
    rw [trace_product,Matrix.trace_sum]
    rfl

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
open TraceHolder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

/- Trace Holder applied separately on every literal placement cycle. -/
theorem trace_block_holder {m : ℕ} [NeZero m] (hm : 0 < m)
    (A : Fin m → Matrix (Ω × n) (Ω × n) ℂ) :
    ‖Matrix.trace (List.ofFn A).prod‖ ≤
      ∑ x : Fin m → Ω, ∏ i, schatten m (blocks (A i) (x i) (x (i+1))) := by
  rw [trace_block_product hm]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => matrix_trace_holder hm _)

/- The exact alternating word for the unnormalized even moment. -/

omit [Nonempty n] in
lemma evenWord_prod (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) :
    (evenWord q A).prod=(A.conjTranspose*A)^q := by
  induction q with
  | zero => simp [evenWord]
  | succ q ih =>
    change ([A.conjTranspose,A]++evenWord q A).prod=_
    simp only [List.prod_append,List.prod_cons,List.prod_nil,mul_one,ih,pow_succ']

omit [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n] in
lemma evenWord_mem (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) {B : Matrix (Ω × n) (Ω × n) ℂ}
    (h : B ∈ evenWord q A) : B=A.conjTranspose ∨ B=A := by
  obtain ⟨l,hl,hm⟩ := List.mem_flatten.mp h
  have he : l=[A.conjTranspose,A] := (List.mem_replicate.mp hl).2
  simpa [he] using hm

/- Literal cyclic index expansion of the induced even moment, before probabilities
and augmented path potentials are substituted. -/
theorem even_moment_blocks (q : ℕ) (hq : 0 < q) (A : Matrix (Ω × n) (Ω × n) ℂ) :
    let L := evenWord q A
    letI : NeZero L.length := ⟨by rw [evenWord_length]; omega⟩
    (Matrix.trace ((A.conjTranspose*A)^q)).re ≤
      ∑ x : Fin L.length → Ω, ∏ i, schatten (2*q) (blocks (L.get i) (x i) (x (i+1))) := by
  let L := evenWord q A
  have hL : 0 < L.length := by dsimp [L]; rw [evenWord_length]; omega
  let : NeZero L.length := ⟨by omega⟩
  have hh := trace_block_holder hL (fun i => L.get i)
  rw [List.ofFn_get] at hh
  have hl : L.length=2*q := evenWord_length q A
  have he : (∑ x : Fin L.length → Ω, ∏ i, schatten L.length (blocks (L.get i) (x i) (x (i+1))))=
      ∑ x : Fin L.length → Ω, ∏ i, schatten (2*q) (blocks (L.get i) (x i) (x (i+1))) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun m => schatten m (blocks (L.get i) (x i) (x (i+1)))) hl
  rw [he] at hh
  have hp : L.prod=(A.conjTranspose*A)^q := evenWord_prod q A
  rw [hp] at hh
  exact (Complex.re_le_norm _).trans hh

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
open TraceHolder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
lemma block_adjoint (A : Matrix (Ω × n) (Ω × n) ℂ) (y x : Ω) :
    blocks A.conjTranspose y x=(blocks A x y).conjTranspose := by ext i j; rfl

omit [Nonempty n] in
lemma edge_block (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (K : Ω → Ω → Matrix n n ℂ) (hA : ∀ y x, blocks A y x=(p y x : ℂ) • K y x)
    (hB : B=A.conjTranspose ∨ B=A) (y x : Ω) :
    blocks B y x=(edgeWeight A B p y x : ℂ) • edgeFiber A B K y x := by
  by_cases h : B=A
  · simp only [edgeWeight,edgeFiber,h]
    exact hA y x
  · obtain hb | hb := hB
    · subst B
      rw [edgeWeight,edgeFiber,ite_eq_right h,ite_eq_right h,block_adjoint,hA,
        Matrix.conjTranspose_smul]
      simp
    · exact (h hb).elim

omit [DecidableEq Ω] [DecidableEq n] [Nonempty n] in
lemma edgeWeight_nonneg (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (hp : ∀ y x, 0 ≤ p y x) (y x : Ω) : 0 ≤ edgeWeight A B p y x := by
  unfold edgeWeight
  split_ifs <;> apply hp

/- Each placement cycle carries exactly the transition probabilities of its
forward or adjoint edges and the unnormalized conditional fiber moments. -/
theorem even_cycle_bound (q : ℕ) (hq : 0 < q) (A : Matrix (Ω × n) (Ω × n) ℂ)
    (p : Ω → Ω → ℝ) (hp : ∀ y x, 0 ≤ p y x) (K : Ω → Ω → Matrix n n ℂ)
    (hA : ∀ y x, blocks A y x=(p y x : ℂ) • K y x) :
    let L := evenWord q A
    letI : NeZero L.length := ⟨by rw [evenWord_length]; omega⟩
    (Matrix.trace ((A.conjTranspose*A)^q)).re ≤
      ∑ x : Fin L.length → Ω,
        (∏ i, edgeWeight A (L.get i) p (x i) (x (i+1))) *
        ∏ i, (Matrix.trace (((edgeFiber A (L.get i) K (x i) (x (i+1))).conjTranspose*
          edgeFiber A (L.get i) K (x i) (x (i+1)))^q)).re ^ ((2*q : ℝ)⁻¹) := by
  let L := evenWord q A
  let : NeZero L.length := ⟨by dsimp [L]; rw [evenWord_length]; omega⟩
  refine (even_moment_blocks q hq A).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _
    exact schatten_nonneg _ _
  · intro i _
    have hB := evenWord_mem q A (List.get_mem L i)
    rw [edge_block A (L.get i) p K hA hB]
    have he := schatten_even_smul_le q hq
      (edgeWeight A (L.get i) p (x i) (x (i+1)) : ℂ)
      (edgeFiber A (L.get i) K (x i) (x (i+1)))
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (edgeWeight_nonneg A (L.get i) p hp _ _)] at he
    simpa only [schatten_even_eq] using he

end CoordinateSweeps.BlockCycles
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Placement_Chart
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
namespace CoordinateSweeps.PlacementInduction
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]

/- A transitive action with actual chosen representatives. For the application,
Ω is the set of ordered placements; the fiber group fixes the base placement. -/

namespace Chart
variable {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma cocycle_inv (g : G) (x : Ω) :
    C.cocycle g⁻¹ (a g x)=(C.cocycle g x)⁻¹ := by
  have hh := C.cocycle_mul g⁻¹ g x
  rw [inv_mul_cancel,C.cocycle_one] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

variable (ρ : UnitaryIrrep C.stabilizer)

/- Literal placement-by-fiber block matrix of the induced unitary action. -/

omit [Fintype G] [Fintype Ω] in
lemma matrix_inv (g : G) : C.matrix ρ g⁻¹=(C.matrix ρ g).conjTranspose := by
  ext y x
  rcases y with ⟨y,i⟩
  rcases x with ⟨x,j⟩
  by_cases he : x=a g y
  · have he' : y=a g⁻¹ x := by
      rw [he,map_inv,Equiv.Perm.coe_inv,Equiv.symm_apply_apply]
    simp only [Matrix.conjTranspose_apply,matrix,ite_eq_left he,ite_eq_left he']
    rw [he,C.cocycle_inv,ρ.matrix_inv]
    rfl
  · have he' : ¬ y=a g⁻¹ x := by
      intro hh
      apply he
      rw [hh,map_inv,Equiv.Perm.coe_inv,Equiv.apply_symm_apply]
    simp only [matrix,ite_eq_right he,ite_eq_right he',Matrix.conjTranspose_apply,star_zero]

omit [Fintype G] in
lemma trace_matrix (g : G) : Matrix.trace (C.matrix ρ g)=
    ∑ x : Ω, if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x)) else 0 := by
  rw [Matrix.trace,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a g x=x
  · simp only [Matrix.diag,matrix,ite_eq_left hx.symm,ite_eq_left hx,Matrix.trace]
  · simp only [Matrix.diag,matrix,ite_eq_right (Ne.symm hx),Finset.sum_const_zero,ite_eq_right hx]

end Chart
end CoordinateSweeps.PlacementInduction

namespace CoordinateSweeps.PlacementInduction.Chart
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [DecidableEq Ω] in
lemma card_group : Fintype.card G=Fintype.card Ω*Fintype.card C.stabilizer := by
  simpa only [Fintype.card_prod] using Fintype.card_congr C.decompose

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma cocycle_fixed (x : Ω) (h : C.stabilizer) :
    C.cocycle ((C.fixedEquiv x h).val) x=h := by
  apply Subtype.ext
  change (C.rep (a (C.fixedEquiv x h).val x))⁻¹*(C.rep x*h.val*(C.rep x)⁻¹)*C.rep x=h.val
  rw [(C.fixedEquiv x h).property]
  group

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [Fintype Ω] in
lemma fixed_character_sum (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G) (x : Ω) :
    (∑ g : G, if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x))*Matrix.trace (τ.matrix g⁻¹) else 0)=
      ∑ h : C.stabilizer, Matrix.trace (ρ.matrix h)*Matrix.trace (τ.matrix (h.val)⁻¹) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun g : G => a g x=x) _ (by intro g; simp) (fun g =>
    Matrix.trace (ρ.matrix (C.cocycle g x))*Matrix.trace (τ.matrix g⁻¹))]
  rw [← (C.fixedEquiv x).sum_comp]
  apply Finset.sum_congr rfl
  intro h _
  rw [C.cocycle_fixed]
  congr 1
  change Matrix.trace (τ.matrix (C.rep x*h.val*(C.rep x)⁻¹)⁻¹)=_
  rw [show (C.rep x*h.val*(C.rep x)⁻¹)⁻¹=C.rep x*h.val⁻¹*(C.rep x)⁻¹ by group]
  exact trace_conj τ.matrix _ _

lemma induced_character_sum (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G) :
    (∑ g : G, Matrix.trace (C.action ρ g)*Matrix.trace (τ.matrix g⁻¹))=
      (Fintype.card Ω : ℂ)*
        ∑ h : C.stabilizer, Matrix.trace (ρ.matrix h)*Matrix.trace (τ.matrix (h.val)⁻¹) := by
  change (∑ g : G, Matrix.trace (C.matrix ρ g)*Matrix.trace (τ.matrix g⁻¹))=_
  simp_rw [C.trace_matrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  have hm (g : G) (x : Ω) :
      (if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x)) else 0)*Matrix.trace (τ.matrix g⁻¹)=
        if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x))*Matrix.trace (τ.matrix g⁻¹) else 0 := by
    split_ifs <;> simp
  simp only [hm,C.fixed_character_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/- Finite Frobenius reciprocity for the literal placement matrices. The RHS
is the actual Hom space in restriction, not an assumed branching coefficient. -/
theorem multiplicity_eq (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G) :
    Module.finrank ℂ (τ.asRepresentation.IntertwiningMap (matrixRepresentation (C.action ρ)))=
      Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) := by
  have hl := τ.character_sum_multiplicity (C.action ρ)
  have hr := ρ.character_sum_multiplicity (τ.matrix.comp C.stabilizer.subtype)
  have he := C.induced_character_sum ρ τ
  have hs : (∑ h : C.stabilizer, Matrix.trace (ρ.matrix h)*Matrix.trace (τ.matrix (h.val)⁻¹))=
      (Fintype.card C.stabilizer : ℂ)*Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) := by
    rw [← hr]
    have hh := Equiv.sum_comp (Equiv.inv C.stabilizer) (fun h : C.stabilizer =>
      Matrix.trace (τ.matrix h.val)*Matrix.trace (ρ.matrix h⁻¹))
    simpa only [Equiv.inv_apply,MonoidHom.comp_apply,Subgroup.subtype_apply,Subgroup.coe_inv,inv_inv,mul_comm]
      using hh
  rw [hs,hl,C.card_group,Nat.cast_mul] at he
  have hcard : (Fintype.card Ω : ℂ)*(Fintype.card C.stabilizer : ℂ) ≠ 0 := by
    rw [← Nat.cast_mul,← C.card_group]
    exact_mod_cast Fintype.card_ne_zero
  have he' := mul_left_cancel₀ hcard (he.trans (mul_assoc _ _ _).symm)
  exact_mod_cast he'

/- The induced moment really dominates each target moment by its branching multiplicity. -/
theorem induced_moment_bound (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G)
    {W : Type*} [Fintype W] (w : W → ℂ) (g : W → G) (q : ℕ) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) : ℝ)*
        (Matrix.trace (((averageMatrix τ.matrix w g).conjTranspose*averageMatrix τ.matrix w g)^q)).re ≤
          (Matrix.trace (((averageMatrix (C.action ρ) w g).conjTranspose*averageMatrix (C.action ρ) w g)^q)).re := by
  rw [← C.multiplicity_eq ρ τ]
  exact τ.multiplicity_moment_le (C.action ρ) (fun g => (C.matrix_inv ρ g).symm) w g q

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [Fintype G] [Fintype Ω] in
lemma transition_nonneg (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω) (g : W → G) (y x : Ω) :
    0 ≤ C.transition w g y x := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_refl 0

omit [Fintype G] in
lemma transition_columns (w : W → ℝ) (hs : ∑ ω, w ω=1) (g : W → G) (x : Ω) :
    ∑ y, C.transition w g y x=1 := by
  unfold transition
  rw [Finset.sum_comm]
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hs

omit [Fintype G] in
lemma transition_rows (w : W → ℝ) (hs : ∑ ω, w ω=1) (g : W → G) (y : Ω) :
    ∑ x, C.transition w g y x=1 := by
  unfold transition
  rw [Finset.sum_comm]
  have he (ω : W) : (∑ x : Ω, if y=a (g ω) x then w ω else 0)=w ω := by
    have hh := Equiv.sum_comp (a (g ω)) (fun x => if y=x then w ω else 0)
    simpa only [Finset.sum_ite_eq,Finset.mem_univ,ite_true] using hh
  simpa only [he] using hs

omit [Fintype G] [Fintype Ω] in
lemma weight_le_transition (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω) (g : W → G)
    (x y : Ω) (ω : W) (hω : y=a (g ω) x) : w ω ≤ C.transition w g y x := by
  have hh := Finset.single_le_sum (s := (Finset.univ : Finset W))
    (f := fun ν => if y=a (g ν) x then w ν else 0)
    (fun ν _ => by split_ifs; exact hw ν; exact le_refl 0) (Finset.mem_univ ω)
  simpa only [transition,ite_eq_left hω] using hh

omit [Fintype G] [Fintype Ω] in
lemma zero_transition_sum (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (g : W → G) (y x : Ω) (hz : C.transition w g y x=0) :
    (∑ ω, if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0)=0 := by
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : y=a (g ω) x
  · have hh := C.weight_le_transition w hw g x y ω hω
    rw [hz] at hh
    have hwz : w ω=0 := le_antisymm hh (hw ω)
    simp [hω,hwz]
  · exact ite_eq_right hω

/- Every induced average block is exactly probability times its actual normalized
conditional fiber operator, including impossible transitions. -/
omit [Fintype G] in
theorem average_block (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (g : W → G) (y x : Ω) :
    (averageMatrix (C.action ρ) (fun ω => (w ω : ℂ)) g).submatrix (fun i => (y,i)) (fun j => (x,j))=
      (C.transition w g y x : ℂ) • C.conditionalBlock ρ w g y x := by
  have he : (averageMatrix (C.action ρ) (fun ω => (w ω : ℂ)) g).submatrix
      (fun i => (y,i)) (fun j => (x,j))=
      ∑ ω, if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0 := by
    ext i j
    simp only [averageMatrix,Matrix.submatrix_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro ω _
    change (w ω : ℂ)*(if y=a (g ω) x then ρ.matrix (C.cocycle (g ω) x) i j else 0)=
      (if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0) i j
    split_ifs <;> simp
  rw [he,conditionalBlock,smul_smul]
  by_cases hz : C.transition w g y x=0
  · rw [C.zero_transition_sum ρ w hw g y x hz,smul_zero]
  · rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hz),one_smul]

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.PlacementInduction.Chart
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma cocycle_residual (x y : Ω) (g₀ g : G) (h₀ : y=a g₀ x) (hg : y=a g x) :
    C.cocycle g x=C.cocycle g₀ x*(C.pointEquiv x).symm (C.transitionResidual x y g₀ g h₀ hg) := by
  apply Subtype.ext
  change (C.rep (a g x))⁻¹*g*C.rep x=
    ((C.rep (a g₀ x))⁻¹*g₀*C.rep x)*((C.rep x)⁻¹*(g₀⁻¹*g)*C.rep x)
  rw [← hg,← h₀]
  group

/- Normalized residual law on the true point stabilizer. The reference is any
compatible transition; it is a unitary frame, not a new hypothesis on the law. -/
omit [Fintype G] [Fintype Ω] in
theorem conditionalBlock_eq (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (g : W → G)
    (x y : Ω) (ω₀ : W) (h₀ : y=a (g ω₀) x) :
    C.conditionalBlock ρ w g y x=ρ.matrix (C.cocycle (g ω₀) x)*C.transitionAverage ρ w g x y ω₀ h₀ := by
  unfold conditionalBlock transitionAverage
  rw [Matrix.mul_smul,Matrix.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun ω => y=a (g ω) x) (Finset.univ.filter (fun ω => y=a (g ω) x))
    (by intro ω; simp)]
  apply Finset.sum_congr rfl
  intro ω _
  change (w ω.val : ℂ) • ρ.matrix (C.cocycle (g ω.val) x)=
    ρ.matrix (C.cocycle (g ω₀) x)*((w ω.val : ℂ) •
      ρ.matrix ((C.pointEquiv x).symm (C.transitionResidual x y (g ω₀) (g ω.val) h₀ ω.property)))
  rw [Matrix.mul_smul,← map_mul]
  congr 2
  exact C.cocycle_residual x y (g ω₀) (g ω.val) h₀ ω.property

end CoordinateSweeps.PlacementInduction.Chart

end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_PlacementMoment
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

namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma augmented_residual (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ω : {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x}) :
    H.augmentFixEquiv u x (fun i => G.sweep ω₀.val (x i).val) ω₀.val ω₀.property (fun _ => rfl)
      ((H.placementChart u).transitionResidual x (H.placementAction (H.residual hf ω₀) x)
        (H.residual hf ω₀) (H.residual hf ω.val) rfl ω.property)=
      (H.augmented x ω₀).residualWithReference (H.augmentedReference x ω₀)
        (H.augmentedChoices hf x ω₀ ω) := by
  apply Subtype.ext
  change (((G.sweep (H.reference hf))⁻¹*G.sweep ω₀.val)⁻¹*
    ((G.sweep (H.reference hf))⁻¹*G.sweep ω.val.val))=(G.sweep ω₀.val)⁻¹*G.sweep ω.val.val
  group

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma placementWeight_nonneg (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (ω : {ω : G.Choices // H.Compatible ω}) : 0 ≤ H.placementWeight z ω :=
  div_nonneg (G.choiceWeight_pos hz hz' ω.val).le (H.probability_pos hf hz hz').le

lemma placementWeight_sum (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    ∑ ω, H.placementWeight z ω=1 := by
  unfold placementWeight
  rw [← Finset.sum_div]
  exact div_self (H.probability_pos hf hz hz').ne'

/- Transition probability in the induced representation is the exact conditional
probability of the augmented path family. -/
theorem transition_probability (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) (z : ℝ) :
    (H.placementChart u).transition (H.placementWeight z) (H.residual hf)
      (H.placementAction (H.residual hf ω₀) x) x=
      (H.augmented x ω₀).probability z/H.probability z := by
  classical
  let : Fintype {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x} := Subtype.fintype _
  have he : (∑ ω : {ω : G.Choices // H.Compatible ω},
      if H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x
      then G.choiceWeight z ω.val else 0)=(H.augmented x ω₀).probability z := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun ω : {ω : G.Choices // H.Compatible ω} =>
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x)
      _ (by intro ω; simp)]
    exact Equiv.sum_comp (H.augmentedChoices hf x ω₀) (fun ω => G.choiceWeight z ω.val)
  unfold PlacementInduction.Chart.transition placementWeight
  rw [← he,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma augmentedIrrep_residual (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer)
    (ω : {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x}) :
    (H.augmentedIrrep u x ω₀ ρ).matrix
      ((H.augmented x ω₀).residualWithReference (H.augmentedReference x ω₀)
        (H.augmentedChoices hf x ω₀ ω))=
      ρ.matrix ((H.placementChart u).pointEquiv x |>.symm <|
        (H.placementChart u).transitionResidual x (H.placementAction (H.residual hf ω₀) x)
          (H.residual hf ω₀) (H.residual hf ω.val) rfl ω.property) := by
  change ρ.matrix ((H.placementChart u).pointEquiv x |>.symm <|
    (H.augmentFixEquiv u x (fun i => G.sweep ω₀.val (x i).val) ω₀.val ω₀.property (fun _ => rfl)).symm
      ((H.augmented x ω₀).residualWithReference (H.augmentedReference x ω₀)
        (H.augmentedChoices hf x ω₀ ω)))=_
  rw [← H.augmented_residual hf u x ω₀ ω,MulEquiv.symm_apply_apply]

/- Actual normalized placement-fiber average equals the augmented sweep average
in a feasible frame. No conditional law is extended to complex z. -/
theorem transitionAverage_eq_augmented (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    (H.placementChart u).transitionAverage ρ (H.placementWeight z) (H.residual hf)
      x (H.placementAction (H.residual hf ω₀) x) ω₀ rfl=
      (H.augmented x ω₀).averageWithReference (H.augmentedReference x ω₀) z (H.augmentedIrrep u x ω₀ ρ) := by
  classical
  let : Fintype {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x} := Subtype.fintype _
  unfold PlacementInduction.Chart.transitionAverage averageWithReference
  rw [H.transition_probability hf u x ω₀ z,Finset.smul_sum]
  rw [← Equiv.sum_comp (H.augmentedChoices hf x ω₀)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [H.augmentedIrrep_residual hf u x ω₀ ρ ω,smul_smul]
  congr 1
  change ((↑((H.augmented x ω₀).probability z/H.probability z) : ℂ)⁻¹*
    ↑(G.choiceWeight z ω.val.val/H.probability z))=↑(G.choiceWeight z ω.val.val/(H.augmented x ω₀).probability z)
  have hH : (H.probability z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (H.probability_pos hf hz hz').ne'
  have hJ : ((H.augmented x ω₀).probability z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((H.augmented x ω₀).probability_pos (H.augmented_feasible x ω₀) hz hz').ne'
  push_cast
  field_simp

/- The original conditional fiber moment in06:eq23, with the full augmented path
potential available from03:eq4. All frame factors are proved unitary. -/
theorem conditionalBlock_augmented_moment (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) (q : ℕ) :
    schattenMoment q ((H.placementChart u).conditionalBlock ρ (H.placementWeight z) (H.residual hf)
      (H.placementAction (H.residual hf ω₀) x) x)=
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep u x ω₀ ρ)) := by
  rw [(H.placementChart u).conditionalBlock_eq ρ (H.placementWeight z) (H.residual hf) x _ ω₀ rfl]
  rw [schattenMoment_unitary_left q _ _ (ρ.unitary _),H.transitionAverage_eq_augmented hf u x ω₀ ρ hz hz']
  exact (H.augmented x ω₀).averageWithReference_moment (H.augmented_feasible x ω₀)
    (H.augmentedReference x ω₀) z (H.augmentedIrrep u x ω₀ ρ) q

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma augmented_extends (x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) : (H.augmented x ω₀).Extends H :=
  H.augment_extends _ _ _ _ _ _

/- The uniform hook estimate is charged to each actual induced block using
source03:eq4. This is the precise attachment, not a new assumption about frames. -/
theorem augmented_block_budget (hf : H.Feasible) (u : H.Placement (k := k))
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz'.le g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz'.le g ≤ 2*FiniteLaw.uniform _ g)
    (q : ℕ) (B : ℝ)
    (hT : ∀ (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}),
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep u x ω₀ ρ)) ≤ Real.exp (B-(H.augmented x ω₀).cost))
    (y x : H.Placement (k := k)) :
    (H.placementChart u).transition (H.placementWeight z) (H.residual hf) y x*
      schattenMoment q ((H.placementChart u).conditionalBlock ρ (H.placementWeight z) (H.residual hf) y x)
      ≤ Real.exp (B-(k : ℝ)*Real.log G.size-H.cost+Real.log 4*k*G.b) := by
  by_cases he : ∃ ω₀ : {ω : G.Choices // H.Compatible ω}, y=H.placementAction (H.residual hf ω₀) x
  · obtain ⟨ω₀,rfl⟩ := he
    rw [H.conditionalBlock_augmented_moment hf u x ω₀ ρ hz hz',H.transition_probability hf u x ω₀ z]
    have hp := (H.augmented x ω₀).conditional_transition_bound H (H.augmented_extends x ω₀) hz hz'.le hlo hhi
    calc
      _ ≤ ((H.augmented x ω₀).probability z/H.probability z)*Real.exp (B-(H.augmented x ω₀).cost) :=
        mul_le_mul_of_nonneg_left (hT x ω₀) (div_nonneg
          ((H.augmented x ω₀).probability_pos (H.augmented_feasible x ω₀) hz hz').le
          (H.probability_pos hf hz hz').le)
      _ ≤ _ := (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; congr 1; ring)
  · have hp : (H.placementChart u).transition (H.placementWeight z) (H.residual hf) y x=0 := by
      apply Finset.sum_eq_zero
      intro ω _
      exact ite_eq_right (fun hh => he ⟨ω,hh⟩)
    rw [hp,zero_mul]
    exact (Real.exp_pos _).le
end CoordinateSweeps.Grid.Holes

/- Required analytic interpolation for the matrix trace Hölder step06 (23).
A bounded holomorphic function on a tube over a box is bounded on the tube
over the convex hull of its bounded vertices. No Schatten assertion assumed. -/
noncomputable section
open Set Complex
open scoped BigOperators Topology

open scoped Matrix.Norms.L2Operator

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

variable {Ω : Type*} [Fintype Ω]

theorem sum_tuple_split (n : ℕ) (f : (Fin (n+1) → Ω) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x, f (Fin.cons a x) := by
  rw [← (tupleSplit n).symm.sum_comp f]
  exact Fintype.sum_prod_type _

omit [Fintype Ω] in
theorem chainWeight_succ {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+2) → Ω) :
    chainWeight P x = P 0 (x 0) (x 1) *
      chainWeight (fun i => P i.succ) (fun i => x i.succ) := by
  rw [chainWeight, Fin.prod_univ_succ]
  rfl

theorem sum_chainWeight {n : ℕ} (P : Fin n → Ω → Ω → ℝ)
    (hP : ∀ i y, ∑ x, P i x y = 1) :
    ∑ x, chainWeight P x = Fintype.card Ω := by
  induction n with
  | zero => simp [chainWeight]
  | succ n ih =>
    rw [sum_tuple_split, Finset.sum_comm]
    simp only [chainWeight_succ, Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
    simp_rw [← Finset.sum_mul, hP 0, one_mul]
    apply ih
    intro i y
    exact hP i.succ y

/- The edge-deleted product from the source; the missing edge is represented
by 1, so the empty/one-node case is unambiguous. -/

omit [Fintype Ω] in
theorem deletedCycle_last {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+1) → Ω) :
    deletedCycle P x (Fin.last n) = chainWeight (fun i => P i.castSucc) x := by
  rw [deletedCycle, Fin.prod_univ_castSucc]
  simp [chainWeight, Fin.castSucc_ne_last]

omit [Fintype Ω] in
theorem deletedCycle_rotate {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+1) → Ω) (r : Fin (n+1)) :
    let e := finCycle (r-Fin.last n)
    deletedCycle P x r =
      deletedCycle (fun i => P (e i)) (tupleReindex e x) (Fin.last n) := by
  intro e
  have he : e (Fin.last n) = r := by dsimp [e]; simp
  unfold deletedCycle
  rw [← Equiv.prod_comp e (fun i => if i = r then 1 else P i (x i) (x (i+1)))]
  apply Finset.prod_congr rfl
  intro i _
  have hiff : e i = r ↔ i = Fin.last n := by rw [← he, Equiv.apply_eq_iff_eq]
  simp only [hiff]
  by_cases hi : i = Fin.last n
  · simp [hi]
  · simp only [hi, ite_false, tupleReindex, Equiv.coe_fn_mk]
    congr 2
    dsimp [e]
    simp only [finCycle_apply]
    abel

theorem sum_deletedCycle {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (hP : ∀ i y, ∑ x, P i x y = 1) (r : Fin (n+1)) :
    ∑ x, deletedCycle P x r = Fintype.card Ω := by
  let e := finCycle (r-Fin.last n)
  calc
    _ = ∑ x, deletedCycle (fun i => P (e i)) (tupleReindex e x) (Fin.last n) := by
      apply Finset.sum_congr rfl
      intro x _
      exact deletedCycle_rotate P x r
    _ = ∑ y, deletedCycle (fun i => P (e i)) y (Fin.last n) := Equiv.sum_comp (tupleReindex e) (fun y => deletedCycle (fun i => P (e i)) y (Fin.last n))
    _ = ∑ y, chainWeight (fun i => P (e i.castSucc)) y := by simp_rw [deletedCycle_last]
    _ = _ := sum_chainWeight _ (fun i y => hP _ y)

/- The product identity retains zeros, so the eventual inequality does not
silently omit impossible cyclic placement terms. -/
theorem prod_deleted_numbers {n : ℕ} (p : Fin (n+1) → ℝ) :
    (∏ r, ∏ i, if i = r then (1 : ℝ) else p i) = (∏ i, p i)^n := by
  rw [Finset.prod_comm, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  have he := Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin (n+1))))
    (f := fun r => if i = r then (1 : ℝ) else p i) (Finset.mem_univ i)
  simp only [ite_true, mul_one] at he
  rw [← he]
  calc
    _ = ∏ _ ∈ (Finset.univ : Finset (Fin (n+1))).erase i, p i := by
      apply Finset.prod_congr rfl
      intro r hr
      exact ite_eq_right (Ne.symm (Finset.mem_erase.mp hr).1)
    _ = _ := by simp

theorem cycle_geometric_identity {n : ℕ} (p : Fin (n+1) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∏ i, (p i)^((n : ℝ)/(n+1))) =
      ∏ r, (∏ i, if i = r then (1 : ℝ) else p i)^((n+1 : ℝ)⁻¹) := by
  have hn : 0 ≤ ∏ i, p i := Finset.prod_nonneg (fun i _ => hp i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hp i), Real.finsetProd_rpow _ _ (by
    intro r _
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · positivity
    · exact hp i), prod_deleted_numbers,
    ← Real.rpow_natCast (∏ i, p i) n, ← Real.rpow_mul hn]
  congr 1

/- Exact scalar cycle bound used after (23); column stochasticity alone
suffices. The paper has both row and column stochasticity from bijections. -/
theorem stochastic_cycle_holder {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (hP0 : ∀ i x y, 0 ≤ P i x y) (hP : ∀ i y, ∑ x, P i x y = 1) :
    (∑ x : Fin (n+1) → Ω, ∏ i, (P i (x i) (x (i+1)))^((n : ℝ)/(n+1))) ≤
      Fintype.card Ω := by
  have hN : (n+1 : ℝ) ≠ 0 := by positivity
  have hweights : (∑ _ : Fin (n+1), (n+1 : ℝ)⁻¹) = 1 := by simp [hN]
  calc
    _ ≤ ∑ x : Fin (n+1) → Ω, ∑ r, (n+1 : ℝ)⁻¹ * deletedCycle P x r := by
      apply Finset.sum_le_sum
      intro x _
      rw [cycle_geometric_identity _ (fun i => hP0 i _ _)]
      apply Real.geom_mean_le_arith_mean_weighted
      · intro _ _; positivity
      · exact hweights
      · intro r _
        apply Finset.prod_nonneg
        intro i _
        split_ifs
        · positivity
        · exact hP0 i _ _
    _ = Fintype.card Ω := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_deletedCycle P hP]
      simp [hN]

end CoordinateSweeps

namespace CoordinateSweeps
variable {Ω : Type*} [Fintype Ω]

/- Archived scalar cycle inequality with the positive cycle length explicit. -/
theorem stochastic_cycle_holder_length {N : ℕ} [NeZero N]
    (P : Fin N → Ω → Ω → ℝ) (hP0 : ∀ i x y, 0 ≤ P i x y)
    (hP : ∀ i y, ∑ x, P i x y=1) :
    (∑ x : Fin N → Ω, ∏ i, (P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹)) ≤ Fintype.card Ω := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have he : 1-(n+1 : ℝ)⁻¹=(n : ℝ)/(n+1) := by field_simp; ring
    simpa only [Nat.cast_add,Nat.cast_one,he] using stochastic_cycle_holder P hP0 hP

lemma weighted_root_le {p t E r : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t) (hE : 0 ≤ E)
    (hr : 0 < r) (hh : p*t ≤ E) :
    p*t^r ≤ E^r*p^(1-r) := by
  by_cases hp0 : p=0
  · subst p
    simp only [zero_mul]
    positivity
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  calc
    p*t^r=(p*t)^r*p^(1-r) := by
      rw [Real.mul_rpow hp ht]
      have he : p^r*p^(1-r)=p := by rw [← Real.rpow_add hp',add_sub_cancel,Real.rpow_one]
      calc
        _ = (p^r*p^(1-r))*t^r := by rw [he]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (mul_nonneg hp ht) hh hr.le)
      (Real.rpow_nonneg hp _)

/- Source06:eq24 scalar endgame, with the full trajectory potential charged
once locally as P*T ≤ E. No independence or positivity of edges is assumed. -/
theorem cycle_potential_bound {N : ℕ} [NeZero N]
    (P T : Fin N → Ω → Ω → ℝ) (hP0 : ∀ i y x, 0 ≤ P i y x)
    (hT0 : ∀ i y x, 0 ≤ T i y x) (hP : ∀ i x, ∑ y, P i y x=1)
    {E : ℝ} (hE : 0 ≤ E) (hPT : ∀ i y x, P i y x*T i y x ≤ E) :
    (∑ x : Fin N → Ω, (∏ i, P i (x i) (x (i+1))) *
      ∏ i, (T i (x i) (x (i+1)))^((N : ℝ)⁻¹)) ≤ (Fintype.card Ω : ℝ)*E := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  calc
    _ ≤ ∑ x : Fin N → Ω, E*∏ i, (P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro x _
      rw [← Finset.prod_mul_distrib]
      calc
        _ ≤ ∏ i, E^((N : ℝ)⁻¹)*(P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹) := by
          apply Finset.prod_le_prod
          · intro i _; exact mul_nonneg (hP0 i _ _) (Real.rpow_nonneg (hT0 i _ _) _)
          · intro i _; exact weighted_root_le (hP0 i _ _) (hT0 i _ _) hE (inv_pos.mpr hN) (hPT i _ _)
        _ = _ := by
          rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
          congr 1
          rw [← Real.rpow_natCast,← Real.rpow_mul hE,inv_mul_cancel₀ hN.ne',Real.rpow_one]
    _ = E*∑ x : Fin N → Ω, ∏ i, (P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ E*Fintype.card Ω := mul_le_mul_of_nonneg_left (stochastic_cycle_holder_length P hP0 hP) hE
    _ = _ := mul_comm _ _
end CoordinateSweeps

namespace CoordinateSweeps.BlockCycles
open TraceHolder
open scoped ComplexOrder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq Ω] [DecidableEq n] [Nonempty n] in
lemma edgeWeight_columns (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (hc : ∀ x, ∑ y, p y x=1) (hr : ∀ y, ∑ x, p y x=1) (x : Ω) :
    ∑ y, edgeWeight A B p y x=1 := by
  unfold edgeWeight
  split_ifs <;> first | exact hc x | exact hr x

omit [DecidableEq Ω] [Nonempty n] in
lemma edge_moment_nonneg (A B : Matrix (Ω × n) (Ω × n) ℂ)
    (K : Ω → Ω → Matrix n n ℂ) (q : ℕ) (y x : Ω) :
    0 ≤ (Matrix.trace (((edgeFiber A B K y x).conjTranspose*edgeFiber A B K y x)^q)).re :=
  (((Matrix.posSemidef_conjTranspose_mul_self (edgeFiber A B K y x)).pow q).trace_nonneg).1

omit [DecidableEq Ω] [Nonempty n] in
lemma edge_potential (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (K : Ω → Ω → Matrix n n ℂ) (q : ℕ) (E : ℝ)
    (hPT : ∀ y x, p y x*(Matrix.trace (((K y x).conjTranspose*K y x)^q)).re ≤ E) (y x : Ω) :
    edgeWeight A B p y x*
      (Matrix.trace (((edgeFiber A B K y x).conjTranspose*edgeFiber A B K y x)^q)).re ≤ E := by
  unfold edgeWeight edgeFiber
  split_ifs
  · exact hPT y x
  · rw [Matrix.conjTranspose_conjTranspose,trace_mul_pow_comm]
    exact hPT x y

/- The genuine matrix placement-cycle bound closes using the literal doubly
stochastic transitions and source03's potential budget. -/
theorem even_potential_bound (q : ℕ) (hq : 0 < q) (A : Matrix (Ω × n) (Ω × n) ℂ)
    (p : Ω → Ω → ℝ) (hp : ∀ y x, 0 ≤ p y x)
    (hc : ∀ x, ∑ y, p y x=1) (hr : ∀ y, ∑ x, p y x=1)
    (K : Ω → Ω → Matrix n n ℂ)
    (hA : ∀ y x, blocks A y x=(p y x : ℂ) • K y x)
    {E : ℝ} (hE : 0 ≤ E)
    (hPT : ∀ y x, p y x*(Matrix.trace (((K y x).conjTranspose*K y x)^q)).re ≤ E) :
    (Matrix.trace ((A.conjTranspose*A)^q)).re ≤ (Fintype.card Ω : ℝ)*E := by
  let L := evenWord q A
  let : NeZero L.length := ⟨by dsimp [L]; rw [evenWord_length]; omega⟩
  refine (even_cycle_bound q hq A p hp K hA).trans ?_
  have hb := cycle_potential_bound (N := L.length)
    (fun i => edgeWeight A (L.get i) p)
    (fun i y x => (Matrix.trace (((edgeFiber A (L.get i) K y x).conjTranspose*
      edgeFiber A (L.get i) K y x)^q)).re)
    (fun i => edgeWeight_nonneg A (L.get i) p hp)
    (fun i => edge_moment_nonneg A (L.get i) K q)
    (fun i => edgeWeight_columns A (L.get i) p hc hr) hE
    (fun i => edge_potential A (L.get i) p K q E hPT)
  have he : ((L.length : ℝ)⁻¹)=((2*q : ℝ)⁻¹) := by dsimp [L]; rw [evenWord_length]; push_cast; rfl
  rw [he] at hb
  exact hb
end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep BlockCycles
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

theorem induced_potential_bound (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G)
    (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω=1) (g : W → G)
    (q : ℕ) (hq : 0 < q) {E : ℝ} (hE : 0 ≤ E)
    (hPT : ∀ y x, C.transition w g y x *
      (Matrix.trace (((C.conditionalBlock ρ w g y x).conjTranspose*C.conditionalBlock ρ w g y x)^q)).re ≤ E) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) : ℝ)*
        (Matrix.trace (((averageMatrix τ.matrix (fun ω => (w ω : ℂ)) g).conjTranspose*
          averageMatrix τ.matrix (fun ω => (w ω : ℂ)) g)^q)).re ≤ (Fintype.card Ω : ℝ)*E := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  refine (C.induced_moment_bound ρ τ (fun ω => (w ω : ℂ)) g q).trans ?_
  exact even_potential_bound q hq _ (C.transition w g) (C.transition_nonneg w hw g)
    (C.transition_columns w hs g) (C.transition_rows w hs g) _
    (C.average_block ρ w hw g) hE hPT
end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma placements_card_le : Fintype.card (H.Placement (k := k)) ≤ G.size^k := by
  rw [Fintype.card_embedding_eq,H.card_freeAt, Fintype.card_fin]
  exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

/- Source06:eq24's entire placement-counting and potential endgame, with true
branching Hom multiplicity and arbitrary feasible holes. The hook estimate is
its sole analytic input and will be discharged by the child induction. -/
theorem actual_induced_endgame (hf : H.Feasible) (u : H.Placement (k := k))
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) (τ : UnitaryIrrep H.stabilizer)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz'.le g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz'.le g ≤ 2*FiniteLaw.uniform _ g)
    (q : ℕ) (hq : 0 < q) (B : ℝ)
    (hT : ∀ (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}),
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep u x ω₀ ρ)) ≤ Real.exp (B-(H.augmented x ω₀).cost)) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (τ.matrix.comp (H.placementChart u).stabilizer.subtype))) : ℝ)*
        schattenMoment q (H.conditionalAverage hf z τ) ≤
      Real.exp (B-H.cost+Real.log 4*k*G.b) := by
  have hh := (H.placementChart u).induced_potential_bound ρ τ (H.placementWeight z)
    (H.placementWeight_nonneg hf hz hz') (H.placementWeight_sum hf hz hz') (H.residual hf) q hq
    (Real.exp_pos (B-(k : ℝ)*Real.log G.size-H.cost+Real.log 4*k*G.b)).le
    (H.augmented_block_budget hf u ρ hz hz' hlo hhi q B hT)
  have hav : averageMatrix τ.matrix (fun ω => (H.placementWeight z ω : ℂ)) (H.residual hf)=
      H.conditionalAverage hf z τ := by rw [H.conditionalAverage_eq_sum]; rfl
  rw [hav] at hh
  refine hh.trans ?_
  have hs : 0 < (G.size : ℝ) := by
    have hsN : 0<G.size := by
      unfold Grid.size
      exact Finset.prod_pos (fun j _ => pow_pos (by omega : 0<2) _)
    exact_mod_cast hsN
  calc
    _ ≤ (G.size : ℝ)^k*Real.exp (B-(k : ℝ)*Real.log G.size-H.cost+Real.log 4*k*G.b) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast H.placements_card_le (k := k)) (Real.exp_pos _).le
    _ = _ := by
      rw [show (G.size : ℝ)^k=Real.exp ((k : ℝ)*Real.log G.size) by
        rw [Real.exp_nat_mul,Real.exp_log hs],← Real.exp_add]
      congr 1
      ring
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
-- module Solutions.OAIQ56_CS.Young_Restriction
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
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.CommutingRestriction
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- The action of a commuting group on the multiplicity space. -/

lemma homAction_fixedSum {Y : Type*} [Fintype Y] [DecidableEq Y]
    (τ : Representation ℂ G V) (σ : Representation ℂ (Equiv.Perm Y) V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W)
    (color : Y → ℕ) (f : ρ.IntertwiningMap τ) (w : W) :
    (YoungCorner.fixedSum color (homAction τ σ hc ρ) f) w=YoungCorner.fixedSum color σ (f w) := by
  simp [YoungCorner.fixedSum,Representation.IntertwiningMap.sum_apply]

lemma homAction_alternatingSum {Y : Type*} [Fintype Y] [DecidableEq Y]
    (τ : Representation ℂ G V) (σ : Representation ℂ (Equiv.Perm Y) V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W)
    (color : Y → ℕ) (f : ρ.IntertwiningMap τ) (w : W) :
    (YoungCorner.alternatingSum color (homAction τ σ hc ρ) f) w=
      YoungCorner.alternatingSum color σ (f w) := by
  simp [YoungCorner.alternatingSum,Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply]

lemma sum_intertwine {Y : Type*} [Fintype Y] [DecidableEq Y]
    (τ : Representation ℂ G V) (σ : Representation ℂ (Equiv.Perm Y) V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (f g : Y → ℕ) (x : G) :
    Commute (τ x) (YoungCorner.fixedSum f σ * YoungCorner.alternatingSum g σ) := by
  apply Commute.mul_right
  · apply Commute.sum_right
    intro y hy
    exact hc x y
  · apply Commute.sum_right
    intro y hy
    exact (hc x y).smul_right _

end CoordinateSweeps.CommutingRestriction

namespace CoordinateSweeps.CommutingRestriction
open YoungCorner
variable {X Y V Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z]

/- Exact multiplicity lower bound from two commuting Young corners for the
removed-hook argument. -/
theorem joint_corner_multiplicity (τ : Representation ℂ (Equiv.Perm X) V)
    (σ : Representation ℂ (Equiv.Perm Y) V) (hc : ∀ g h, Commute (τ g) (σ h))
    (μ ν : YoungDiagram) (t : X ≃ Boxes μ) (u : Y ≃ Boxes ν)
    (δ : Representation ℂ (Equiv.Perm Y) Z) [δ.IsIrreducible] (hδ : hasShape ν u δ)
    (hne : (fixedSum (rowColor t) τ * alternatingSum (colColor t) τ) *
      (fixedSum (rowColor u) σ * alternatingSum (colColor u) σ) ≠ 0) :
    ∃ S : Subrepresentation τ, S.toRepresentation.IsIrreducible ∧ hasShape μ t S.toRepresentation ∧
      Module.finrank ℂ Z ≤ Module.finrank ℂ (S.toRepresentation.IntertwiningMap τ) := by
  let A := fixedSum (rowColor t) τ * alternatingSum (colColor t) τ
  let B := fixedSum (rowColor u) σ * alternatingSum (colColor u) σ
  have hAB : Commute A B := by
    apply Commute.mul_left
    · apply Commute.sum_left
      intro g hg
      exact sum_intertwine τ σ hc _ _ g
    · apply Commute.sum_left
      intro g hg
      exact (sum_intertwine τ σ hc _ _ g).smul_left _
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting τ (A*B) hne
  have hShape : hasShape μ t S.toRepresentation := by
    intro hz
    have hh:=congrArg (fun L : Module.End ℂ S.toSubmodule => (L v : V)) hz
    simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hh
    have hAv : A (v : V)=0 := hh
    apply hv
    rw [hAB.eq]
    simp only [Module.End.mul_apply,hAv,map_zero]
  let υ := homAction τ σ hc S.toRepresentation
  have hν : hasShape ν u υ := by
    intro hz
    have hh:=congrArg (fun L : Module.End ℂ (S.toRepresentation.IntertwiningMap τ) =>
      (L (inclusion τ S)) v) hz
    simp only [υ,Module.End.mul_apply,homAction_fixedSum,homAction_alternatingSum] at hh
    have hBv : B (v : V)=0 := hh
    apply hv
    simp only [Module.End.mul_apply,hBv,map_zero]
  obtain ⟨T,hT,w,hw⟩ := RepDetection.exists_irreducible_detecting υ
    (fixedSum (rowColor u) υ*alternatingSum (colColor u) υ) hν
  have hTshape : hasShape ν u T.toRepresentation := by
    intro hz
    apply hw
    have hh:=congrArg (fun L : Module.End ℂ T.toSubmodule => (L w : S.toRepresentation.IntertwiningMap τ)) hz
    simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hh
    exact hh
  let := hT
  obtain ⟨e⟩ := equiv_of_same_shape δ T.toRepresentation ν u u hδ hTshape
  refine ⟨S,hS,hShape,?_⟩
  rw [e.toLinearEquiv.finrank_eq]
  exact Submodule.finrank_le T.toSubmodule

end CoordinateSweeps.CommutingRestriction

namespace CoordinateSweeps.YoungCorner
variable {X Y Z A : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] [Ring A] [Algebra ℂ A]

lemma signScalar_ne_zero (g : Equiv.Perm X) : signScalar g ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h|h <;> simp [signScalar,h]

lemma fixedSum_absorb (f : X → ℕ) (g : Y → ℕ) (τ : Equiv.Perm X →* A)
    (φ : Equiv.Perm Y →* Equiv.Perm X)
    (hφ : ∀ r : colorStabilizer g, φ r.val ∈ colorStabilizer f) :
    fixedSum f τ * fixedSum g (τ.comp φ)=
      (Fintype.card (colorStabilizer g) : ℂ) • fixedSum f τ := by
  change fixedSum f τ * (∑ r : colorStabilizer g, τ (φ r.val))=_
  rw [Finset.mul_sum]
  have he (r : colorStabilizer g) : fixedSum f τ * τ (φ r.val)=fixedSum f τ :=
    fixedSum_right f τ ⟨φ r.val,hφ r⟩
  simp only [he,Finset.sum_const,Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

lemma alternatingSum_absorb (f : X → ℕ) (g : Y → ℕ) (τ : Equiv.Perm X →* A)
    (φ : Equiv.Perm Y →* Equiv.Perm X)
    (hφ : ∀ c : colorStabilizer g, φ c.val ∈ colorStabilizer f)
    (hs : ∀ c : Equiv.Perm Y, signScalar (φ c)=signScalar c) :
    alternatingSum g (τ.comp φ) * alternatingSum f τ=
      (Fintype.card (colorStabilizer g) : ℂ) • alternatingSum f τ := by
  change (∑ c : colorStabilizer g, signScalar c.val • τ (φ c.val))*alternatingSum f τ=_
  rw [Finset.sum_mul]
  have he (c : colorStabilizer g) : (signScalar c.val • τ (φ c.val))*alternatingSum f τ=alternatingSum f τ := by
    rw [smul_mul_assoc,alternatingSum_left f τ ⟨φ c.val,hφ c⟩]
    change signScalar c.val • (signScalar (φ c.val))⁻¹ • alternatingSum f τ=_
    rw [hs,smul_smul,mul_inv_cancel₀ (signScalar_ne_zero _),one_smul]
  simp only [he,Finset.sum_const,Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

/- A split of the row and column stabilizers preserves a nonzero Young corner. -/
lemma joint_of_full_corner (τ : Equiv.Perm X →* A)
    (fR fC : X → ℕ) (gR gC : Y → ℕ) (hR hC : Z → ℕ)
    (φ : Equiv.Perm Y →* Equiv.Perm X) (ψ : Equiv.Perm Z →* Equiv.Perm X)
    (hφR : ∀ r : colorStabilizer gR, φ r.val ∈ colorStabilizer fR)
    (hφC : ∀ c : colorStabilizer gC, φ c.val ∈ colorStabilizer fC)
    (hψR : ∀ r : colorStabilizer hR, ψ r.val ∈ colorStabilizer fR)
    (hψC : ∀ c : colorStabilizer hC, ψ c.val ∈ colorStabilizer fC)
    (hφs : ∀ g : Equiv.Perm Y, signScalar (φ g)=signScalar g)
    (hψs : ∀ g : Equiv.Perm Z, signScalar (ψ g)=signScalar g)
    (hcomm : ∀ g h, Commute (φ g) (ψ h))
    (hne : fixedSum fR τ * alternatingSum fC τ ≠ 0) :
    (fixedSum gR (τ.comp φ)*alternatingSum gC (τ.comp φ)) *
      (fixedSum hR (τ.comp ψ)*alternatingSum hC (τ.comp ψ)) ≠ 0 := by
  let P : A :=fixedSum fR τ
  let Q : A :=alternatingSum fC τ
  let PR : A :=fixedSum gR (τ.comp φ)
  let QR : A :=alternatingSum gC (τ.comp φ)
  let PC : A :=fixedSum hR (τ.comp ψ)
  let QC : A :=alternatingSum hC (τ.comp ψ)
  let a : ℂ:=Fintype.card (colorStabilizer gR)
  let b : ℂ:=Fintype.card (colorStabilizer hR)
  let c : ℂ:=Fintype.card (colorStabilizer gC)
  let d : ℂ:=Fintype.card (colorStabilizer hC)
  have hP : P*PR=a•P := fixedSum_absorb fR gR τ φ hφR
  have hP' : P*PC=b•P := fixedSum_absorb fR hR τ ψ hψR
  have hQ : QR*Q=c•Q := alternatingSum_absorb fC gC τ φ hφC hφs
  have hQ' : QC*Q=d•Q := alternatingSum_absorb fC hC τ ψ hψC hψs
  have hcross : Commute QR PC := by
    apply Commute.sum_left
    intro g hg
    apply Commute.smul_left
    apply Commute.sum_right
    intro h hh
    exact (hcomm g.val h.val).map τ
  have he : P*((PR*QR)*(PC*QC))*Q=(a*b*d*c) • (P*Q) := by
    calc
      _ = ((P*PR)*PC)*(QR*(QC*Q)) := by
        simp only [mul_assoc]
        rw [← mul_assoc QR PC, hcross.eq]
        simp only [mul_assoc]
      _ = (a*b*d*c) • (P*Q) := by
        rw [hP,smul_mul_assoc,hP',hQ',mul_smul_comm,hQ]
        simp only [smul_smul,smul_mul_assoc,mul_smul_comm]
        congr 1
        ring
  intro hz
  change (PR*QR)*(PC*QC)=0 at hz
  rw [hz,mul_zero,zero_mul] at he
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer gR))
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer hR))
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer gC))
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer hC))
  exact (smul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hd) hc) hne) he.symm

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

variable {X Y Z : Type*}

lemma splitPerm_commute (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) (h : Equiv.Perm Z) :
    Commute (leftPerm e g) (rightPerm e h) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩:=e.surjective x
  cases y <;> simp

lemma leftPerm_rows (μ : YoungDiagram) (p : ℕ) (r : rows (hookPart μ p)) :
    leftPerm (boxesSplit μ p) r.val ∈ rows μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simpa only [leftPerm_inl,boxesSplit_inl] using r.property y
  | inr y => simp only [leftPerm_inr]

lemma leftPerm_cols (μ : YoungDiagram) (p : ℕ) (c : cols (hookPart μ p)) :
    leftPerm (boxesSplit μ p) c.val ∈ cols μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simpa only [leftPerm_inl,boxesSplit_inl] using c.property y
  | inr y => simp only [leftPerm_inr]

lemma rightPerm_rows (μ : YoungDiagram) (p : ℕ) (r : rows (removedPart μ p)) :
    rightPerm (boxesSplit μ p) r.val ∈ rows μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simp only [rightPerm_inl]
  | inr y => simpa only [rightPerm_inr,boxesSplit_inr,shifted] using congrArg (·+p) (r.property y)

lemma rightPerm_cols (μ : YoungDiagram) (p : ℕ) (c : cols (removedPart μ p)) :
    rightPerm (boxesSplit μ p) c.val ∈ cols μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simp only [rightPerm_inl]
  | inr y => simpa only [rightPerm_inr,boxesSplit_inr,shifted] using congrArg (·+p) (c.property y)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma rectangle_card_le (μ : YoungDiagram) (x : Boxes μ) :
    (x.val.1+1)*(x.val.2+1)≤Fintype.card (Boxes μ) := by
  let f (a : Fin (x.val.1+1) × Fin (x.val.2+1)) : Boxes μ :=
    ⟨(a.1.val,a.2.val),μ.up_left_mem (Nat.le_of_lt_succ a.1.isLt) (Nat.le_of_lt_succ a.2.isLt) x.property⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z : Boxes μ => z.val.1) he
    · exact congrArg (fun z : Boxes μ => z.val.2) he
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma removedPart_rank_lt (μ : YoungDiagram) (p : ℕ) (x : Boxes (removedPart μ p)) :
    x.val.1+x.val.2 < 2*(Fintype.card (Boxes μ)/(p+1)) := by
  have hr:=rectangle_card_le μ ⟨shifted p x.val,(mem_removedPart μ p _).mp x.property⟩
  change (x.val.1+p+1)*(x.val.2+p+1)≤Fintype.card (Boxes μ) at hr
  have h₁ : (x.val.1+1)*(p+1)≤Fintype.card (Boxes μ) := by
    apply le_trans _ hr
    apply Nat.mul_le_mul <;> omega
  have h₂ : (x.val.2+1)*(p+1)≤Fintype.card (Boxes μ) := by
    rw [Nat.mul_comm] at hr
    apply le_trans _ hr
    apply Nat.mul_le_mul <;> omega
  have h₁' := (Nat.le_div_iff_mul_le (by omega : 0<p+1)).mpr h₁
  have h₂' := (Nat.le_div_iff_mul_le (by omega : 0<p+1)).mpr h₂
  omega

lemma hookPart_property (μ : YoungDiagram) (p : ℕ) (x : Boxes (hookPart μ p)) :
    x.val.1<p ∨ x.val.2<p := ((mem_hookPart μ p x.val).mp x.property).2

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

lemma signScalar_leftPerm (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) :
    signScalar (leftPerm e g)=signScalar g := by
  simp [signScalar,leftPerm,Equiv.Perm.sign_permCongr,Equiv.Perm.sign_sumCongr]

lemma signScalar_rightPerm (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Z) :
    signScalar (rightPerm e g)=signScalar g := by
  simp [signScalar,rightPerm,Equiv.Perm.sign_permCongr,Equiv.Perm.sign_sumCongr]

lemma hook_removed_joint {A : Type*} [Ring A] [Algebra ℂ A]
    (μ : YoungDiagram) (p : ℕ) (τ : Equiv.Perm (Boxes μ) →* A)
    (hμ : fixedSum (fun x : Boxes μ => x.val.1) τ * alternatingSum (fun x : Boxes μ => x.val.2) τ ≠ 0) :
    (fixedSum (fun x : Boxes (hookPart μ p) => x.val.1) (τ.comp (leftPerm (boxesSplit μ p))) *
      alternatingSum (fun x : Boxes (hookPart μ p) => x.val.2) (τ.comp (leftPerm (boxesSplit μ p)))) *
    (fixedSum (fun x : Boxes (removedPart μ p) => x.val.1) (τ.comp (rightPerm (boxesSplit μ p))) *
      alternatingSum (fun x : Boxes (removedPart μ p) => x.val.2) (τ.comp (rightPerm (boxesSplit μ p)))) ≠ 0 :=
  joint_of_full_corner τ _ _ _ _ _ _ _ _
    (leftPerm_rows μ p) (leftPerm_cols μ p) (rightPerm_rows μ p) (rightPerm_cols μ p)
    (signScalar_leftPerm _) (signScalar_rightPerm _) (splitPerm_commute _) hμ

/- Retained-hook multiplicity for the hook part and translated removed partition. -/
theorem hook_removed_multiplicity {V W : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (μ : YoungDiagram) (p : ℕ) (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V)
    (hτ : hasShape μ (Equiv.refl _) τ)
    (δ : Representation ℂ (Equiv.Perm (Boxes (removedPart μ p))) W) [δ.IsIrreducible]
    (hδ : hasShape (removedPart μ p) (Equiv.refl _) δ) :
    ∃ S : Subrepresentation (τ.comp (leftPerm (boxesSplit μ p))),
      S.toRepresentation.IsIrreducible ∧ hasShape (hookPart μ p) (Equiv.refl _) S.toRepresentation ∧
      Module.finrank ℂ W ≤ Module.finrank ℂ
        (S.toRepresentation.IntertwiningMap (τ.comp (leftPerm (boxesSplit μ p)))) := by
  apply CommutingRestriction.joint_corner_multiplicity
    (τ.comp (leftPerm (boxesSplit μ p))) (τ.comp (rightPerm (boxesSplit μ p)))
    (fun g h => (splitPerm_commute (boxesSplit μ p) g h).map τ)
    (hookPart μ p) (removedPart μ p) (Equiv.refl _) (Equiv.refl _) δ hδ
  exact hook_removed_joint μ p τ hτ

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RestrictionBound
variable {Ω I V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [Fintype Ω] [DecidableEq Ω] [FiniteDimensional ℂ V] in
lemma orbit_span_top (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (v : V) (hv : v ≠ 0) : Submodule.span ℂ (Set.range (fun g => ρ g v))=⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range (fun g => ρ g v))
      apply_mem_toSubmodule := by
        intro g w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k,rfl⟩:=hw
          apply Submodule.subset_span
          exact ⟨g*k,by simp only [map_mul,Module.End.mul_apply]⟩
        | zero => simp
        | add x y hx hy ix iy => simpa only [map_add] using Submodule.add_mem _ ix iy
        | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih }
  have hn : S ≠ ⊥ := by
    intro he
    have hm : v ∈ S := Submodule.subset_span ⟨1,by simp⟩
    rw [he] at hm
    exact hv hm
  exact congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top S).resolve_left hn)

/- A pointwise-stabilizer constituent generates at most n^k copies of its
vector space. This is the exact logarithmic dimension upper bound in06:eq22. -/
theorem dimension_le_pow_mul (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (a : I → Ω) (W : Submodule ℂ V) (hW : W ≠ ⊥)
    (hstable : ∀ g : Equiv.Perm Ω, (∀ i, g (a i)=a i) → ∀ w ∈ W, ρ g w ∈ W) :
    Module.finrank ℂ V ≤ (Fintype.card Ω)^(Fintype.card I)*Module.finrank ℂ W := by
  classical
  have hn : ∃ v ∈ W, v ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hW
    apply bot_unique
    intro v hv
    exact hh v hv
  obtain ⟨v,hvW,hv⟩:=hn
  let restrict (g : Equiv.Perm Ω) : I → Ω := fun i => g (a i)
  let chooseG (x : I → Ω) : Equiv.Perm Ω := if hx : ∃ g, restrict g=x then hx.choose else 1
  have hchoose (g : Equiv.Perm Ω) : restrict (chooseG (restrict g))=restrict g := by
    simp only [chooseG,dite_eq_left (show ∃ t, restrict t=restrict g from ⟨g,rfl⟩)]
    exact Exists.choose_spec (show ∃ t, restrict t=restrict g from ⟨g,rfl⟩)
  let b := Module.finBasis ℂ W
  let u (x : (I → Ω) × Fin (Module.finrank ℂ W)) : V := ρ (chooseG x.1) (b x.2).val
  have hspan : Submodule.span ℂ (Set.range u)=⊤ := by
    rw [eq_top_iff,← orbit_span_top ρ v hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    let r:=chooseG (restrict g)
    have hfix : ∀ i, (r⁻¹*g) (a i)=a i := by
      intro i
      have he:=congrFun (hchoose g) i
      change r (a i)=g (a i) at he
      simp only [Equiv.Perm.mul_apply]
      rw [← he]
      simp
    let w : W := ⟨ρ (r⁻¹*g) v,hstable _ hfix _ hvW⟩
    have he : ρ g v=ρ r w.val := by
      change ρ g v=ρ r (ρ (r⁻¹*g) v)
      rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel_left]
    change ρ g v ∈ Submodule.span ℂ (Set.range u)
    rw [he,← b.sum_repr w]
    simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(restrict g,i),rfl⟩
  have hd:=finrank_le_of_span_eq_top hspan
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] using hd

end CoordinateSweeps.RestrictionBound

namespace CoordinateSweeps.YoungCorner
/- The retained hook gives a dimension upper bound (source06:eq22). -/
theorem hook_dimension_upper {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (μ : YoungDiagram) (p : ℕ)
    (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V) [τ.IsIrreducible]
    (S : Subrepresentation (τ.comp (leftPerm (boxesSplit μ p)))) (hS : S ≠ ⊥) :
    Module.finrank ℂ V ≤ (Fintype.card (Boxes μ))^(Fintype.card (Boxes (removedPart μ p))) *
      Module.finrank ℂ S.toSubmodule := by
  apply RestrictionBound.dimension_le_pow_mul τ
    (fun z => boxesSplit μ p (Sum.inr z)) S.toSubmodule
  · intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  · intro g hg w hw
    obtain ⟨f,rfl⟩ := leftPerm_range_of_fix_right (boxesSplit μ p) g hg
    exact S.apply_mem_toSubmodule f hw
end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X Y V : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup V] [Module ℂ V]
lemma fixedSum_reparam (e : X ≃ Y) (f : Y → ℕ) (τ : Representation ℂ (Equiv.Perm Y) V) :
    fixedSum (fun x => f (e x)) (τ.comp e.permCongrHom)=fixedSum f τ := by
  exact Fintype.sum_equiv (colorEquiv e f).toEquiv _ _ (fun _ => rfl)
lemma alternatingSum_reparam (e : X ≃ Y) (f : Y → ℕ) (τ : Representation ℂ (Equiv.Perm Y) V) :
    alternatingSum (fun x => f (e x)) (τ.comp e.permCongrHom)=alternatingSum f τ := by
  apply Fintype.sum_equiv (colorEquiv e f).toEquiv
  intro g
  change signScalar g.val • τ (e.permCongrHom g.val)=signScalar (e.permCongrHom g.val) • τ (e.permCongrHom g.val)
  congr 1
  simp [signScalar]
lemma hasShape_reparam (μ : YoungDiagram) (e : X ≃ Y) (t : Y ≃ Boxes μ)
    (τ : Representation ℂ (Equiv.Perm Y) V) :
    hasShape μ (e.trans t) (τ.comp e.permCongrHom) ↔ hasShape μ t τ := by
  unfold hasShape
  change fixedSum (fun x => rowColor t (e x)) (τ.comp e.permCongrHom)*
      alternatingSum (fun x => colColor t (e x)) (τ.comp e.permCongrHom) ≠ 0 ↔ _
  rw [fixedSum_reparam,alternatingSum_reparam]
end CoordinateSweeps.YoungCorner

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
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Attachment
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
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)

lemma retained_restrict (τ : UnitaryIrrep H.stabilizer) :
    (matrixRepresentation (τ.matrix.comp (H.placementChart (H.removedPlacement μ p e)).stabilizer.subtype)).comp
        (H.retainedEquiv μ p e).toMonoidHom=
      (τ.pullback (H.boxesChart μ e)).asRepresentation.comp (leftPerm (boxesSplit μ p)) := rfl

/- Source06:eq22 and genuine retained-hook Hom multiplicity simultaneously,
on the literal placement stabilizer used by the conditional induced cycle. -/
theorem exists_retained_irrep (τ : UnitaryIrrep H.stabilizer)
    (hτ : hasShape μ (Equiv.refl _) (τ.pullback (H.boxesChart μ e)).asRepresentation) :
    ∃ ρ : UnitaryIrrep (H.placementChart (H.removedPlacement μ p e)).stabilizer,
      hasShape (hookPart μ p) (Equiv.refl _)
        (ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom) ∧
      Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule ≤
        Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
          (matrixRepresentation (τ.matrix.comp (H.placementChart (H.removedPlacement μ p e)).stabilizer.subtype))) ∧
      τ.dimension ≤ (Fintype.card (Boxes μ))^(Fintype.card (Boxes (removedPart μ p)))*ρ.dimension := by
  let τB := (τ.pullback (H.boxesChart μ e)).asRepresentation
  let δ := (shapeSubrep (removedPart μ p) (Equiv.refl _)).toRepresentation
  obtain ⟨S,hSi,hSh,hm⟩ := hook_removed_multiplicity μ p τB hτ δ (shapeSubrep_hasShape _ _)
  let : S.toRepresentation.IsIrreducible := hSi
  obtain ⟨σ,⟨eS⟩⟩ := UnitaryRealization.exists_unitary S.toRepresentation
  have hSdim : Module.finrank ℂ S.toSubmodule=σ.dimension := by
    have hh := eS.toLinearEquiv.finrank_eq
    simpa using hh
  have hS : S ≠ ⊥ := by
    intro hh
    rw [hh] at hSdim
    have hz : Module.finrank ℂ (⊥ : Submodule ℂ (Fin τ.dimension → ℂ))=0 := by simp
    have he : σ.dimension=0 := hSdim.symm.trans hz
    exact σ.positive.ne' he
  let ρ := σ.pullback (H.retainedEquiv μ p e).symm
  have hρ : ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom=σ.asRepresentation := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change σ.asRepresentation ((H.retainedEquiv μ p e).symm (H.retainedEquiv μ p e g)) v=σ.asRepresentation g v
    rw [MulEquiv.symm_apply_apply]
  refine ⟨ρ,?_,?_,?_⟩
  · rw [hρ]
    exact hasShape_equiv _ _ _ _ eS hSh
  · have hsource := (Representation.IntertwiningMap.sourceEquiv eS
        (τB.comp (leftPerm (boxesSplit μ p)))).finrank_eq
    have hreparam := (Representation.IntertwiningMap.reparamEquiv ρ.asRepresentation
      (matrixRepresentation (τ.matrix.comp (H.placementChart (H.removedPlacement μ p e)).stabilizer.subtype))
        (H.retainedEquiv μ p e)).finrank_eq
    rw [hρ,H.retained_restrict μ p e τ] at hreparam
    exact hm.trans_eq (hsource.trans hreparam.symm)
  · have hh := hook_dimension_upper μ p τB S hS
    rw [hSdim] at hh
    change Module.finrank ℂ (Fin τ.dimension → ℂ) ≤ _ at hh
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hh
    exact hh
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
lemma retainedMap_site (g : Equiv.Perm (Boxes (hookPart μ p))) (a : Boxes (hookPart μ p)) :
    H.stabilizerFreeEquiv (H.retainedMap μ p e g) (H.retainedSite μ p e a)=H.retainedSite μ p e (g a) := by
  change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
    (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g))) (e.symm (boxesSplit μ p (Sum.inl a)))=_
  rw [MulEquiv.apply_symm_apply]
  simp [leftPerm,retainedSite]
  rfl

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
lemma augmentedRetainedChart_eq
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) (g : Equiv.Perm (Boxes (hookPart μ p))) :
    H.augmentedRetainedChart μ p e x ω₀ g=
      H.augmentFixEquiv (H.removedPlacement μ p e) x (fun i => G.sweep ω₀.val (x i).val)
        ω₀.val ω₀.property (fun _ => rfl)
        ((H.placementChart (H.removedPlacement μ p e)).pointEquiv x (H.retainedEquiv μ p e g)) := by
  apply (H.augmented x ω₀).stabilizerFreeEquiv.injective
  change (H.augmented x ω₀).stabilizerFreeEquiv
    ((H.augmented x ω₀).stabilizerFreeEquiv.symm ((H.augmentedRetainedEquiv μ p e x ω₀).permCongrHom g))=_
  rw [MulEquiv.apply_symm_apply]
  apply Equiv.ext
  intro y
  obtain ⟨a,rfl⟩ := (H.augmentedRetainedEquiv μ p e x ω₀).surjective y
  apply Subtype.ext
  change ((H.augmentedRetainedEquiv μ p e x ω₀)
    (g ((H.augmentedRetainedEquiv μ p e x ω₀).symm ((H.augmentedRetainedEquiv μ p e x ω₀) a)))).val=_
  rw [Equiv.symm_apply_apply]
  change ((H.placementChart (H.removedPlacement μ p e)).rep x).val ((H.retainedSite μ p e (g a)).val)=
    (((H.placementChart (H.removedPlacement μ p e)).rep x).val *
      (H.retainedMap μ p e g).val * (((H.placementChart (H.removedPlacement μ p e)).rep x).val)⁻¹)
      (((H.placementChart (H.removedPlacement μ p e)).rep x).val ((H.retainedSite μ p e a).val))
  simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  have hh := congrArg Subtype.val (H.retainedMap_site μ p e g a)
  change (H.retainedMap μ p e g).val ((H.retainedSite μ p e a).val)=(H.retainedSite μ p e (g a)).val at hh
  rw [hh]

/- The transported fiber is the same retained Young type on the *actual*
remaining sites. This rules out any unsupported abstract symmetric-group relabeling. -/
theorem augmented_hasShape
    (ρ : UnitaryIrrep (H.placementChart (H.removedPlacement μ p e)).stabilizer)
    (hρ : hasShape (hookPart μ p) (Equiv.refl _)
      (ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom))
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    hasShape (hookPart μ p) (Equiv.refl _)
      ((H.augmentedIrrep (H.removedPlacement μ p e) x ω₀ ρ).pullback
        (H.augmentedRetainedChart μ p e x ω₀)).asRepresentation := by
  have he : ((H.augmentedIrrep (H.removedPlacement μ p e) x ω₀ ρ).pullback
        (H.augmentedRetainedChart μ p e x ω₀)).asRepresentation=
      ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change Matrix.toLinAlgEquiv' ((H.augmentedIrrep (H.removedPlacement μ p e) x ω₀ ρ).matrix
      (H.augmentedRetainedChart μ p e x ω₀ g))=Matrix.toLinAlgEquiv' (ρ.matrix (H.retainedEquiv μ p e g))
    rw [H.augmentedRetainedChart_eq]
    change Matrix.toLinAlgEquiv' (ρ.matrix
      (((H.placementChart (H.removedPlacement μ p e)).pointEquiv x).symm
        ((H.augmentFixEquiv (H.removedPlacement μ p e) x (fun i => G.sweep ω₀.val (x i).val)
          ω₀.val ω₀.property (fun _ => rfl)).symm
          ((H.augmentFixEquiv (H.removedPlacement μ p e) x (fun i => G.sweep ω₀.val (x i).val)
            ω₀.val ω₀.property (fun _ => rfl))
            ((H.placementChart (H.removedPlacement μ p e)).pointEquiv x (H.retainedEquiv μ p e g))))))=_
    simp only [MulEquiv.symm_apply_apply]
  rw [he]
  exact hρ
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

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
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Scales
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

namespace CoordinateSweeps.Grid
/- Any cut retains exactly the ordered bit list; no coordinate permutation is
introduced into the sweep law. -/
lemma exists_concat_of_length (G : Grid) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hb : G.b=n+m) : ∃ A B : Grid, A.b=n ∧ B.b=m ∧ concat A B=G := by
  rcases G with ⟨b,hpos,bits⟩
  dsimp only at hb
  subst b
  let A : Grid := ⟨n,hn,fun i => bits (Fin.castAdd m i)⟩
  let B : Grid := ⟨m,hm,fun i => bits (Fin.natAdd n i)⟩
  refine ⟨A,B,rfl,rfl,?_⟩
  have he : Fin.addCases A.bits B.bits=bits := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [A]
    | right i => simp [B]
  change Grid.mk (n+m) _ (Fin.addCases A.bits B.bits)=Grid.mk (n+m) _ bits
  rw [he]

/- Cutting the coordinate list in half is balanced because every bit count is
between r and 2r. This avoids choosing a cut by logarithmic rounding. -/
lemma exists_half_concat (G : Grid) (hb : 2 ≤ G.b) :
    ∃ A B : Grid, concat A B=G ∧ A.b<G.b ∧ B.b<G.b ∧ A.b≤B.b ∧ B.b≤2*A.b := by
  let n := G.b/2
  let m := G.b-n
  have hn : 0 < n := by dsimp [n]; omega
  have hm : 0 < m := by dsimp [m,n]; omega
  obtain ⟨A,B,hA,hB,hG⟩ := G.exists_concat_of_length n m hn hm (by dsimp [n,m]; omega)
  refine ⟨A,B,hG,?_,?_,?_,?_⟩
  all_goals simp only [hA,hB]
  all_goals (dsimp [n,m] at *; omega)

-- Reused archived grid logarithm support (InductionBase:858--881).

lemma balanced_logs {A B : Grid} {r : ℕ} (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) :
    (1/5 : ℝ)*Real.log (concat A B).size ≤ Real.log A.size ∧
    Real.log A.size ≤ (4/5 : ℝ)*Real.log (concat A B).size ∧
    (1/5 : ℝ)*Real.log (concat A B).size ≤ Real.log B.size ∧
    Real.log B.size ≤ (4/5 : ℝ)*Real.log (concat A B).size := by
  rw [concat_size,Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr A.size_pos.ne')
    (Nat.cast_ne_zero.mpr B.size_pos.ne')]
  have ha := A.log_size_lower hA
  have hb := B.log_size_lower hB
  have hau := A.log_size_upper hA
  have hbu := B.log_size_upper hB
  have hab : (A.b : ℝ)≤B.b := by exact_mod_cast hAB
  have hba : (B.b : ℝ)≤2*A.b := by exact_mod_cast hBA
  have hr : 0 ≤ (r : ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hab' := mul_le_mul_of_nonneg_right hab hr
  have hba' := mul_le_mul_of_nonneg_right hba hr
  have hn := Real.log_nonneg (show (1 : ℝ) ≤ B.size by exact_mod_cast B.size_pos)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma balanced_sizes {A B : Grid} {r : ℕ} (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) :
    ((concat A B).size : ℝ)^((1:ℝ)/5) ≤ A.size ∧
    (A.size : ℝ) ≤ ((concat A B).size : ℝ)^((4:ℝ)/5) ∧
    ((concat A B).size : ℝ)^((1:ℝ)/5) ≤ B.size ∧
    (B.size : ℝ) ≤ ((concat A B).size : ℝ)^((4:ℝ)/5) := by
  have hh := balanced_logs hA hB hAB hBA
  have hs : (0:ℝ)<(concat A B).size := Nat.cast_pos.mpr (concat A B).size_pos
  have ha : (0:ℝ)<A.size := Nat.cast_pos.mpr A.size_pos
  have hb : (0:ℝ)<B.size := Nat.cast_pos.mpr B.size_pos
  rw [Real.rpow_def_of_pos hs,Real.rpow_def_of_pos hs]
  constructor
  · simpa only [Real.exp_log ha,mul_comm] using Real.exp_le_exp.mpr hh.1
  constructor
  · simpa only [Real.exp_log ha,mul_comm] using Real.exp_le_exp.mpr hh.2.1
  constructor
  · simpa only [Real.exp_log hb,mul_comm] using Real.exp_le_exp.mpr hh.2.2.1
  · simpa only [Real.exp_log hb,mul_comm] using Real.exp_le_exp.mpr hh.2.2.2
end CoordinateSweeps.Grid
end

noncomputable section
open scoped BigOperators
open Filter Asymptotics
namespace CoordinateSweeps
-- Literal source constants (ConditionalTarget:509--514), not new hypotheses.

namespace ScalarInduction
/- A fixed polynomial logarithmic loss is uniformly negligible compared
with any strictly larger power, the quantitative choice needed in06. -/
theorem removed_endgame (L F Fg Fd k h b C : ℝ) (_ : ℝ) (err : ℝ)
    (hL : 0 < L) (_ : 0 ≤ F) (hh : 0 ≤ h) (_ : 0 ≤ k)
    (hD : F ≤ Fg+k*L) (hroot : 0 < Real.sqrt L)
    (hcost : (c0+e0)*k*L+Real.log 4*k*b-Fd+err ≤ F/(20*Real.sqrt L)) :
    -(c0+1/Real.sqrt L+1/(20*Real.sqrt L))*Fg+
      (e0-1/Real.sqrt L-1/(20*Real.sqrt L))*(h+k)*L+err-C+Real.log 4*k*b-Fd ≤
      -(c0+1/Real.sqrt L)*F+(e0-1/Real.sqrt L)*h*L-C := by
  have hc0 : 0 ≤ c0 := by norm_num [c0,a]
  have hc : 0 ≤ c0+1/Real.sqrt L+1/(20*Real.sqrt L) :=
    add_nonneg (add_nonneg hc0 (one_div_nonneg.mpr hroot.le)) (by positivity)
  have hmain := mul_le_mul_of_nonneg_left hD hc
  have hhole : 0 ≤ (1/(20*Real.sqrt L))*h*L := by positivity
  have hscale : (1/(20*Real.sqrt L))*F=F/(20*Real.sqrt L) := by ring
  rw [← hscale] at hcost
  nlinarith

/- Child coefficient improvement from a balanced nontrivial split. -/
lemma reciprocal_sqrt_gap {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t ≤ (4/5)*L) :
    (11/10 : ℝ)/Real.sqrt L ≤ 1/Real.sqrt t := by
  have hLr := Real.sqrt_pos.mpr hL
  have htr := Real.sqrt_pos.mpr ht
  have hsqL := Real.sq_sqrt hL.le
  have hsqt := Real.sq_sqrt ht.le
  apply (div_le_div_iff₀ hLr htr).mpr
  nlinarith [sq_nonneg ((11/10 : ℝ)*Real.sqrt t-Real.sqrt L)]

lemma hook_comparison {L F h cStar eStar E : ℝ} (hL : 0 < L) (hF : 0 ≤ F) (hh : 0 ≤ h)
    (hc : c0+1/Real.sqrt L+1/(20*Real.sqrt L) ≤ cStar)
    (he : eStar+cStar/L ≤ e0-1/Real.sqrt L-1/(20*Real.sqrt L)) :
    -cStar*F+eStar*h*L+cStar*h+E ≤
      -(c0+1/Real.sqrt L+1/(20*Real.sqrt L))*F+
        (e0-1/Real.sqrt L-1/(20*Real.sqrt L))*h*L+E := by
  have h1 := mul_le_mul_of_nonneg_right hc hF
  have h2 := mul_le_mul_of_nonneg_right he (mul_nonneg hh hL.le)
  have heq : cStar/L*(h*L)=cStar*h := by field_simp
  rw [add_mul,heq] at h2
  nlinarith
end ScalarInduction
end CoordinateSweeps
end

noncomputable section
open scoped BigOperators
open Filter Asymptotics
namespace CoordinateSweeps.ScalarInduction
lemma hook_error_bound {s : ℝ} (hs : 1 < s) (q A B p : ℕ) (cStar : ℝ)
    (hc : 0 ≤ cStar) (hc' : cStar ≤ 2*c0)
    (hA : (A:ℝ) ≤ s^((4:ℝ)/5)) (hB : (B:ℝ) ≤ s^((4:ℝ)/5))
    (hp : (p:ℝ) ≤ s^a) :
    (((2*q+1:ℕ):ℝ)*((A+B)*((2*p)*(2*p)):ℕ)+cStar*((A+B)*(41*p^2):ℕ))*Real.log (s+1) ≤
    (((2*q+1:ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*Real.log (s+1) := by
  have hs0 : 0 < s := by linarith
  have hp2 : (p:ℝ)^2 ≤ s^(2*a) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg p : (0:ℝ)≤p) hp 2
    rw [← Real.rpow_natCast (s^a) 2,← Real.rpow_mul hs0.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [mul_comm a 2] using hh
  have hAB : (A:ℝ)+B ≤ 2*s^((4:ℝ)/5) := by linarith
  have hc0 : 0 ≤ c0 := by linarith [hc, hc']
  have h := mul_le_mul hAB hp2 (by positivity : (0:ℝ)≤(p:ℝ)^2)
    (by positivity : (0:ℝ)≤2*s^((4:ℝ)/5))
  rw [mul_assoc,←Real.rpow_add hs0] at h
  have h' := mul_le_mul_of_nonneg_left h (show 0≤((2*q+1:ℕ):ℝ)*4+82*c0 by positivity)
  have hc'' := mul_le_mul_of_nonneg_right hc' (show 0≤((A:ℝ)+B)*41*(p:ℝ)^2 by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by linarith : 1≤ s+1))
  push_cast
  push_cast at h'
  nlinarith

lemma improved_coefficients {L t : ℝ} (hL : 0<L) (ht : 0<t) (htL : t≤(4/5)*L) :
    c0+(11/10:ℝ)/Real.sqrt L ≤ c0+1/Real.sqrt t ∧
    e0-1/Real.sqrt t ≤ e0-(11/10:ℝ)/Real.sqrt L := by
  have hh := reciprocal_sqrt_gap hL ht htL
  constructor <;> linarith
lemma hook_strengthening {L : ℝ} (hL : 0<L) (hroot : 2/e0 ≤ Real.sqrt L)
    (hc : c0+(11/10:ℝ)/Real.sqrt L ≤ 2*c0) :
    c0+1/Real.sqrt L+1/(20*Real.sqrt L) ≤ c0+(11/10:ℝ)/Real.sqrt L ∧
    e0-(11/10:ℝ)/Real.sqrt L+(c0+(11/10:ℝ)/Real.sqrt L)/L ≤
      e0-1/Real.sqrt L-1/(20*Real.sqrt L) := by
  have hR : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have hs := Real.sq_sqrt hL.le
  have hsmall : 20*(c0+(11/10:ℝ)/Real.sqrt L) ≤ Real.sqrt L := by
    have hc0 : 40*c0 ≤ 2/e0 := by norm_num [c0,e0,a]
    linarith
  constructor
  · field_simp
    nlinarith
  · have hx : (c0+(11/10:ℝ)/Real.sqrt L)/L ≤ 1/(20*Real.sqrt L) := by
      apply (div_le_div_iff₀ hL (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hsmall hR.le
      nlinarith
    have he : (11/10:ℝ)/Real.sqrt L=1/Real.sqrt L+2/(20*Real.sqrt L) := by field_simp; ring
    rw [he] at hx ⊢
    have hdiv : (2:ℝ)/(20*Real.sqrt L)=2*(1/(20*Real.sqrt L)) := by ring
    rw [hdiv] at hx ⊢
    linarith
end CoordinateSweeps.ScalarInduction

namespace CoordinateSweeps.ScalarInduction
lemma removed_cost_bound {s k b F Fd : ℝ} {q : ℕ}
    (hs : 1 < s) (hk : 0≤k) (hb : 0≤b) (hb' : b≤(e0/4)*Real.log s)
    (hF : s^(1-a/4)≤F) (hFd : 0≤Fd) (hS : MainSizeReady q s)
    (hEnt : s^(1-a/2)≤k → (a/4)*k*Real.log s≤Fd) :
    (c0+e0)*k*Real.log s+Real.log 4*k*b-Fd+s^((9:ℝ)/10) ≤ F/(20*Real.sqrt (Real.log s)) := by
  have hL := Real.log_pos hs
  have hroot : 0<Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hL
  have hl4 : Real.log 4≤3 := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hc : (c0+e0)*k*Real.log s+Real.log 4*k*b ≤ (a/4)*k*Real.log s := by
    have hh := mul_le_mul_of_nonneg_right hl4 (mul_nonneg hk hb)
    have hbK := mul_le_mul_of_nonneg_left hb' hk
    norm_num [c0,e0,a] at hbK ⊢
    nlinarith
  have hR : s^((9:ℝ)/10)+s^(1-a/2)*Real.log s ≤ F/(20*Real.sqrt (Real.log s)) :=
    hS.removed.trans (div_le_div_of_nonneg_right hF (by positivity))
  by_cases h : s^(1-a/2)≤k
  · have ht := hEnt h
    have hp := Real.rpow_nonneg (by linarith : 0≤ s) (1-a/2)
    nlinarith [mul_nonneg hp hL.le]
  · have ht : k*Real.log s ≤ s^(1-a/2)*Real.log s := mul_le_mul_of_nonneg_right (le_of_not_ge h) hL.le
    have hh : (a/4)*k*Real.log s ≤ k*Real.log s := by
      have hkp:=mul_nonneg hk hL.le
      norm_num [a]
      nlinarith
    linarith
end CoordinateSweeps.ScalarInduction
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Young_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Finite Young-corner construction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.YoungCorner
variable {A : Type*} [Ring A] [Algebra ℂ A]

omit [Algebra ℂ A] in
lemma sumRow_right (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (r : rows μ) : sumRow μ ρ * ρ r = sumRow μ ρ := by
  rw [sumRow,Finset.sum_mul]
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight r) _ _ (fun _ => rfl)

lemma sumCol_left (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (c : cols μ) : ρ c * sumCol μ ρ = (signScalar (c : Equiv.Perm (Boxes μ)))⁻¹ • sumCol μ ρ := by
  rw [sumCol,Finset.mul_sum,Finset.smul_sum]
  have hc : signScalar (c : Equiv.Perm (Boxes μ)) ≠ 0 := by
    intro hzero
    have hh : signScalar (c : Equiv.Perm (Boxes μ))*signScalar (c : Equiv.Perm (Boxes μ))⁻¹=1 := by
      rw [← map_mul,mul_inv_cancel,map_one]
    rw [hzero,zero_mul] at hh
    exact zero_ne_one hh
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro d
  change ρ (c : Equiv.Perm (Boxes μ)) * (signScalar (d : Equiv.Perm (Boxes μ)) • ρ (d : Equiv.Perm (Boxes μ))) =
    (signScalar (c : Equiv.Perm (Boxes μ)))⁻¹ • (signScalar ((c : Equiv.Perm (Boxes μ)) * (d : Equiv.Perm (Boxes μ))) • ρ ((c : Equiv.Perm (Boxes μ)) * (d : Equiv.Perm (Boxes μ))))
  rw [mul_smul_comm,smul_smul,map_mul,map_mul,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

lemma swap_mem_rows (μ : YoungDiagram) (x y : Boxes μ) (h : x.val.1=y.val.1) :
    Equiv.swap x y ∈ rows μ := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma swap_mem_cols (μ : YoungDiagram) (x y : Boxes μ) (h : x.val.2=y.val.2) :
    Equiv.swap x y ∈ cols μ := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

/- Transposition cancellation in a Young row/column corner. -/
lemma corner_zero_of_collision (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (σ : Equiv.Perm (Boxes μ)) (x y : Boxes μ) (hxy : x ≠ y)
    (hrow : x.val.1=y.val.1) (hcol : (σ⁻¹ x).val.2=(σ⁻¹ y).val.2) :
    sumRow μ ρ * ρ σ * sumCol μ ρ=0 := by
  let r : rows μ := ⟨Equiv.swap x y,swap_mem_rows μ x y hrow⟩
  let c : cols μ := ⟨Equiv.swap (σ⁻¹ x) (σ⁻¹ y),swap_mem_cols μ _ _ hcol⟩
  have hcxy : σ⁻¹ x ≠ σ⁻¹ y := fun h => hxy ((σ⁻¹).injective h)
  have he : (r : Equiv.Perm (Boxes μ))*σ = σ*(c : Equiv.Perm (Boxes μ)) := by
    apply Equiv.ext
    intro z
    change Equiv.swap x y (σ z) = σ (Equiv.swap (σ⁻¹ x) (σ⁻¹ y) z)
    by_cases hx : z=σ⁻¹ x
    · subst z; simp
    by_cases hy : z=σ⁻¹ y
    · subst z; simp
    have hx' : σ z ≠ x := by
      intro he; apply hx
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    have hy' : σ z ≠ y := by
      intro he; apply hy
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    rw [Equiv.swap_apply_of_ne_of_ne hx hy,Equiv.swap_apply_of_ne_of_ne hx' hy']
  have hc : (signScalar (c : Equiv.Perm (Boxes μ)))⁻¹ = -1 := by rw [show (c : Equiv.Perm (Boxes μ))=Equiv.swap (σ⁻¹ x) (σ⁻¹ y) from rfl,signScalar_swap _ _ hcxy]; norm_num
  have hh : sumRow μ ρ * ρ σ * sumCol μ ρ = -(sumRow μ ρ * ρ σ * sumCol μ ρ) := by
    calc
      _ = (sumRow μ ρ * ρ r)*ρ σ*sumCol μ ρ := by rw [sumRow_right]
      _ = sumRow μ ρ * (ρ σ * ρ c) * sumCol μ ρ := by rw [mul_assoc (sumRow μ ρ) (ρ r) (ρ σ),← map_mul,he,map_mul]
      _ = sumRow μ ρ * ρ σ * (ρ c * sumCol μ ρ) := by simp only [mul_assoc]
      _ = _ := by rw [sumCol_left,hc]; simp
  have htwo : (2 : ℂ) • (sumRow μ ρ * ρ σ * sumCol μ ρ)=0 := by
    rw [two_smul,← eq_neg_iff_add_eq_zero]
    exact hh
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/- The one-dimensional Young corner in every complex matrix representation,
proved by Ferrers sorting. -/
theorem corner_scalar (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A)
    (σ : Equiv.Perm (Boxes μ)) :
    ∃ c : ℂ, sumRow μ ρ * ρ σ * sumCol μ ρ = c • (sumRow μ ρ * sumCol μ ρ) := by
  by_cases h : NoCollision μ σ⁻¹
  · obtain ⟨c,hc,r,hr,he⟩ := factor_column_row μ σ⁻¹ h
    have hi : σ = r⁻¹*c⁻¹ := by rw [← mul_inv_rev,← he,inv_inv]
    refine ⟨(signScalar c⁻¹)⁻¹,?_⟩
    rw [hi,map_mul,← mul_assoc,sumRow_right μ ρ ⟨r⁻¹,(rows μ).inv_mem hr⟩,
      mul_assoc,sumCol_left μ ρ ⟨c⁻¹,(cols μ).inv_mem hc⟩,mul_smul_comm]
  · simp only [NoCollision] at h
    push Not at h
    obtain ⟨x,y,hrow,hcol,hxy⟩ := h
    exact ⟨0,by rw [corner_zero_of_collision μ ρ σ x y hxy hrow hcol,zero_smul]⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RepDetection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

lemma mem_orbitSpan (τ : Representation ℂ G V) (v : V) : v ∈ orbitSpan τ v := by
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

end CoordinateSweeps.RepDetection

namespace CoordinateSweeps.YoungCorner

lemma youngVector_one (μ : YoungDiagram) : youngVector μ 1=1 := by
  have hv : (fixedSum (rowColor (Equiv.refl (Boxes μ))) (regular (Equiv.Perm (Boxes μ))) *
      alternatingSum (colColor (Equiv.refl (Boxes μ))) (regular (Equiv.Perm (Boxes μ)))) (unitVector μ) 1=1 := by
    simp only [fixedSum,alternatingSum,Module.End.mul_apply,LinearMap.sum_apply,regular_apply,
      Finset.sum_apply,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,mul_one,unitVector,
      ← mul_inv_rev,inv_eq_one,row_column_intersection]
    simp [ite_and]
  exact hv

lemma youngVector_ne_zero (μ : YoungDiagram) : youngVector μ ≠ 0 := by
  intro h
  have hh:=youngVector_one μ
  rw [h] at hh
  exact zero_ne_one hh

lemma youngVector_mem (μ : YoungDiagram) : youngVector μ ∈ columnModule μ := by
  change (sumRow μ (regular (Equiv.Perm (Boxes μ)))) (columnGenerator μ) ∈ (columnModule μ).toSubmodule
  simp only [sumRow,LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r hr
  exact (columnModule μ).apply_mem_toSubmodule r (RepDetection.mem_orbitSpan _ _)

lemma sumRow_square (μ : YoungDiagram) {A : Type*} [Ring A] [Algebra ℂ A]
    (ρ : Equiv.Perm (Boxes μ) →* A) :
    sumRow μ ρ * sumRow μ ρ=(Fintype.card (rows μ) : ℂ) • sumRow μ ρ := by
  conv_lhs => rhs; rw [sumRow]
  rw [Finset.mul_sum]
  simp only [sumRow_right,Finset.sum_const,Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

lemma sumRow_youngVector (μ : YoungDiagram) :
    sumRow μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ)=
      (Fintype.card (rows μ) : ℂ) • youngVector μ := by
  have hh:=congrArg (fun A : Module.End ℂ (Equiv.Perm (Boxes μ) → ℂ) => A (columnGenerator μ))
    (sumRow_square μ (regular (Equiv.Perm (Boxes μ))))
  exact hh

lemma rowImage_line (μ : YoungDiagram) (v : columnModule μ) :
    sumRow μ (regular (Equiv.Perm (Boxes μ))) (v : Equiv.Perm (Boxes μ) → ℂ) ∈
      Submodule.span ℂ {youngVector μ} := by
  suffices hh : ∀ w ∈ (columnModule μ).toSubmodule, sumRow μ (regular (Equiv.Perm (Boxes μ))) w ∈
    Submodule.span ℂ {youngVector μ} from hh v v.property
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g,rfl⟩ := hw
    obtain ⟨c,hc⟩ := corner_scalar μ (regular (Equiv.Perm (Boxes μ))) g
    have hh:=congrArg (fun A : Module.End ℂ (Equiv.Perm (Boxes μ) → ℂ) => A (unitVector μ)) hc
    change sumRow μ (regular (Equiv.Perm (Boxes μ)))
      (regular (Equiv.Perm (Boxes μ)) g (columnGenerator μ))=c • youngVector μ at hh
    rw [hh]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  | zero => simp
  | add x y hx hy ix iy => simpa using Submodule.add_mem _ ix iy
  | smul c x hx ix => simpa using Submodule.smul_mem _ c ix

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma col_row_col_eq_one (μ : YoungDiagram) (c d : cols μ) (r : rows μ) :
    (c.val*r.val)*d.val=1 ↔ r=1 ∧ d=c⁻¹ := by
  constructor
  · intro h
    have he : r.val*(d*c).val=1 := by
      calc
        _ = c.val⁻¹*(c.val*r.val*d.val)*c.val := by simp [mul_assoc]
        _ = _ := by rw [h]; simp
    obtain ⟨hr,hd⟩ := (row_column_intersection μ (Equiv.refl _) r (d*c)).mp he
    exact ⟨hr,mul_eq_one_iff_eq_inv.mp hd⟩
  · rintro ⟨rfl,rfl⟩
    simp

lemma col_youngVector_one (μ : YoungDiagram) :
    sumCol μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ) 1=(Fintype.card (cols μ) : ℂ) := by
  simp only [youngVector,columnGenerator,sumRow,sumCol,LinearMap.sum_apply,
    LinearMap.smul_apply,Pi.smul_apply,regular_apply,Finset.sum_apply,smul_eq_mul,
    Finset.mul_sum,mul_one,unitVector]
  simp_rw [← mul_inv_rev,inv_eq_one,col_row_col_eq_one]
  simp only [ite_and]
  have hn (c : cols μ) : signScalar c.val ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign c.val) with h|h <;> simp [signScalar,h]
  simp [mul_inv_cancel₀ (hn _)]

lemma col_youngVector_ne_zero (μ : YoungDiagram) :
    sumCol μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ) ≠ 0 := by
  intro h
  have he := col_youngVector_one μ
  rw [h] at he
  have hc : (Fintype.card (cols μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact hc he.symm

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma spechtSeed_exists (μ : YoungDiagram) :
    ∃ S : Subrepresentation (columnModule μ).toRepresentation,
      S.toRepresentation.IsIrreducible ∧ hasShape μ (Equiv.refl _) S.toRepresentation ∧
      ∃ v : S.toSubmodule, ((v : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=youngVector μ := by
  let T := columnModule μ
  let : AddCommGroup T.toSubmodule := inferInstance
  let P : Module.End ℂ T.toSubmodule := sumRow μ T.toRepresentation
  have hP : P ≠ 0 := by
    intro hz
    have hh:=congrArg (fun A : Module.End ℂ T.toSubmodule =>
      (A ⟨youngVector μ,youngVector_mem μ⟩ : Equiv.Perm (Boxes μ) → ℂ)) hz
    change (fixedSum (A := Module.End ℂ T.toSubmodule) (rowColor (Equiv.refl (Boxes μ))) T.toRepresentation ⟨youngVector μ,youngVector_mem μ⟩ : Equiv.Perm (Boxes μ) → ℂ)=0 at hh
    rw [fixedSum_subrepresentation] at hh
    change sumRow μ (regular (Equiv.Perm (Boxes μ))) (youngVector μ)=0 at hh
    rw [sumRow_youngVector] at hh
    have hc : (Fintype.card (rows μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact youngVector_ne_zero μ ((smul_eq_zero.mp hh).resolve_left hc)
  obtain ⟨S,hS,v,hv⟩:=RepDetection.exists_irreducible_detecting T.toRepresentation P hP
  let : AddCommGroup S.toSubmodule := inferInstance
  have hPmap (w : S.toSubmodule) :
      (((sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation w : S.toSubmodule) : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
        sumRow μ (regular (Equiv.Perm (Boxes μ))) ((w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ) := by
    change ((fixedSum (A := Module.End ℂ S.toSubmodule) (rowColor (Equiv.refl (Boxes μ))) S.toRepresentation w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [fixedSum_subrepresentation,fixedSum_subrepresentation]
    rfl
  have hQmap (w : S.toSubmodule) :
      (((sumCol (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation w : S.toSubmodule) : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
        sumCol μ (regular (Equiv.Perm (Boxes μ))) ((w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ) := by
    change ((alternatingSum (A := Module.End ℂ S.toSubmodule) (colColor (Equiv.refl (Boxes μ))) S.toRepresentation w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [alternatingSum_subrepresentation,alternatingSum_subrepresentation]
    rfl
  have hPv : (P (v : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
      sumRow μ (regular (Equiv.Perm (Boxes μ))) ((v : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ) :=
    fixedSum_subrepresentation (rowColor (Equiv.refl (Boxes μ))) (regular (Equiv.Perm (Boxes μ))) T v
  obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp (rowImage_line μ (v : T.toSubmodule))
  have hcn : c ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at hc
    apply hv
    apply Subtype.ext
    rw [hPv]
    exact hc.symm
  let w : S.toSubmodule := c⁻¹ • sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation v
  have hw : ((w : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=youngVector μ := by
    change c⁻¹ • (((sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation v : S.toSubmodule) : T.toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [hPmap,← hc,smul_smul,inv_mul_cancel₀ hcn,one_smul]
  have hPS : sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation ≠ 0 := by
    intro hz
    have hh:=hPmap v
    rw [hz] at hh
    apply hv
    apply Subtype.ext
    rw [hPv]
    exact hh.symm
  have hQS : sumCol (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation ≠ 0 := by
    intro hz
    have hh:=hQmap w
    rw [hz,hw] at hh
    exact col_youngVector_ne_zero μ hh.symm
  let :=hS
  have hSh : hasShape μ (Equiv.refl _) S.toRepresentation := by
    obtain ⟨g,hg⟩:=RepDetection.exists_cross_nonzero S.toRepresentation _ _ hPS hQS
    obtain ⟨a,ha⟩:=corner_scalar μ S.toRepresentation g
    intro hz
    apply hg
    change sumRow (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation * sumCol (A := Module.End ℂ S.toSubmodule) μ S.toRepresentation=0 at hz
    rw [ha,hz,smul_zero]
  exact ⟨S,hS,hSh,w,hw⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
/- A rank-preserving row-times-column factor has to be the identity.
This gives independent Young vectors for the entire rank stabilizer. -/
lemma rank_row_col (μ : YoungDiagram) (r : rows μ) (c : cols μ)
    (h : ∀ x : Boxes μ, ((r.val*c.val) x).val.1+((r.val*c.val) x).val.2=x.val.1+x.val.2) :
    r=1 ∧ c=1 := by
  let i : Boxes μ → ℝ := fun x => x.val.1
  let j : Boxes μ → ℝ := fun x => x.val.2
  have hr (x : Boxes μ) : i (r.val x)=i x := congrArg (fun m : ℕ => (m : ℝ)) (r.property x)
  have hc (x : Boxes μ) : j (c.val x)=j x := congrArg (fun m : ℕ => (m : ℝ)) (c.property x)
  have hh (x : Boxes μ) : i (c.val x)+j ((r.val*c.val) x)=i x+j x := by
    have hx:=congrArg (fun m : ℕ => (m : ℝ)) (h x)
    simp only [Nat.cast_add] at hx
    change i (r.val (c.val x))+j ((r.val*c.val) x)=i x+j x at hx
    simpa only [hr] using hx
  have hi : ∑ x, i (c.val x)^2=∑ x, i x^2 :=
    Fintype.sum_equiv c.val _ _ (fun _ => rfl)
  have hij₁ : ∑ x, i (c.val x)*j x=∑ x, i x*j x := by
    simpa only [hc] using (Fintype.sum_equiv c.val (fun x => i (c.val x)*j (c.val x)) (fun x => i x*j x) (fun _ => rfl))
  have hij₂ : ∑ x, i (c.val x)*j ((r.val*c.val) x)=∑ x, i x*j x := by
    simpa only [Equiv.Perm.mul_apply,hr] using
      (Fintype.sum_equiv (r.val*c.val) (fun x => i ((r.val*c.val) x)*j ((r.val*c.val) x)) (fun x => i x*j x) (fun _ => rfl))
  have hprod : ∑ x, i (c.val x)*i x=∑ x, i x^2 := by
    have he : ∑ x, (i (c.val x)*i x + i (c.val x)*j x)=
        ∑ x, (i (c.val x)^2+i (c.val x)*j ((r.val*c.val) x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have ht := congrArg (fun z : ℝ => i (c.val x)*z) (hh x)
      nlinarith only [ht]
    simp only [Finset.sum_add_distrib,hi,hij₁,hij₂] at he
    linarith
  have hz : ∑ x, (i (c.val x)-i x)^2=0 := by
    have he : ∑ x, (i (c.val x)-i x)^2=
        (∑ x, i (c.val x)^2)+(∑ x, i x^2)-2*(∑ x, i (c.val x)*i x) := by
      simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [he,hi,hprod]
    ring
  have hci (x : Boxes μ) : i (c.val x)=i x := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (i (c.val x)-i x))).mp hz x (Finset.mem_univ x)
    nlinarith [sq_nonneg (i (c.val x)-i x)]
  have ce : c=1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have hx :=hci x
      dsimp [i] at hx
      exact_mod_cast hx
    · exact c.property x
  subst c
  refine ⟨?_,rfl⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact r.property x
  · have hx:=h x
    have hr:=r.property x
    simpa only [Subgroup.coe_one,mul_one,Equiv.Perm.one_apply,hr,Nat.add_left_cancel_iff] using hx

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma card_perm_le_colors_mul_stabilizer {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] (f : X → Y) :
    (Fintype.card X).factorial ≤ (Fintype.card Y)^(Fintype.card X) * Fintype.card (colorStabilizer f) := by
  let A (g : Equiv.Perm X) : X → Y := fun x => f (g x)
  let rep (y : X → Y) : Equiv.Perm X := if h : ∃ g, A g=y then h.choose else 1
  have hrep (g : Equiv.Perm X) : A (rep (A g))=A g := by
    simp only [rep,dite_eq_left (show ∃ t, A t=A g from ⟨g,rfl⟩)]
    exact Exists.choose_spec (show ∃ t, A t=A g from ⟨g,rfl⟩)
  let enc (g : Equiv.Perm X) : (X → Y) × colorStabilizer f :=
    (A g,⟨g*(rep (A g))⁻¹,by
      intro x
      have hx:=congrFun (hrep g) ((rep (A g))⁻¹ x)
      simpa [A] using hx.symm⟩)
  have hi : Function.Injective enc := by
    intro g h he
    have hA : A g=A h := congrArg Prod.fst he
    have hk : g*(rep (A g))⁻¹=h*(rep (A h))⁻¹ := congrArg (fun z => z.2.val) he
    rw [hA] at hk
    exact mul_right_cancel hk
  have hc:=Fintype.card_le_of_injective enc hi
  simpa only [Fintype.card_perm,Fintype.card_prod,Fintype.card_fun] using hc

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma youngVector_rank_value (μ : YoungDiagram) (g : ranks μ) :
    youngVector μ g.val = if g.val=1 then 1 else 0 := by
  have he (r : rows μ) (c : cols μ) :
      c.val⁻¹*(r.val⁻¹*g.val)=1 ↔ r=1 ∧ c=1 ∧ g.val=1 := by
    constructor
    · intro h
      have hg : g.val=r.val*c.val := by
        calc
          _ = (r.val*c.val)*(c.val⁻¹*(r.val⁻¹*g.val)) := by group
          _ = _ := by rw [h,mul_one]
      obtain ⟨hr,hc⟩:=rank_row_col μ r c (by intro x; rw [← hg]; exact g.property x)
      exact ⟨hr,hc,by simpa [hr,hc] using hg⟩
    · rintro ⟨rfl,rfl,hg⟩
      simp [hg]
  simp only [youngVector,columnGenerator,sumRow,sumCol,LinearMap.sum_apply,
    LinearMap.smul_apply,Pi.smul_apply,regular_apply,Finset.sum_apply,smul_eq_mul,
    unitVector,he]
  simp [ite_and]

lemma rankVectors_eval (μ : YoungDiagram) (u t : ranks μ) :
    regular (Equiv.Perm (Boxes μ)) u.val (youngVector μ) t.val=if u=t then 1 else 0 := by
  change youngVector μ ((u⁻¹*t).val)=_
  rw [youngVector_rank_value]
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,inv_mul_eq_one,Subtype.val_inj]

lemma rankVectors_independent (μ : YoungDiagram) :
    LinearIndependent ℂ (fun u : ranks μ => regular (Equiv.Perm (Boxes μ)) u.val (youngVector μ)) := by
  apply linearIndependent_iff'.mpr
  intro s a he t ht
  have hh:=congrFun he t.val
  simp only [Finset.sum_apply,Pi.smul_apply,rankVectors_eval,Pi.zero_apply,smul_eq_mul] at hh
  simpa [mul_ite,Finset.sum_ite_eq',ht] using hh

lemma rank_card_le_shape_finrank (μ : YoungDiagram) {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V)
    [τ.IsIrreducible] (hτ : hasShape μ (Equiv.refl _) τ) :
    Fintype.card (ranks μ) ≤ Module.finrank ℂ V := by
  obtain ⟨S,hS,hShape,v,hv⟩:=spechtSeed_exists μ
  let:=hS
  let : AddCommGroup (columnModule μ).toSubmodule := inferInstance
  let : AddCommGroup S.toSubmodule := inferInstance
  obtain ⟨e⟩:=equiv_of_same_shape τ S.toRepresentation μ (Equiv.refl _) (Equiv.refl _) hτ hShape
  rw [e.toLinearEquiv.finrank_eq]
  let f (g : ranks μ) : S.toSubmodule := S.toRepresentation g.val v
  have hmap (g : ranks μ) : ((f g : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=
      regular (Equiv.Perm (Boxes μ)) g.val (youngVector μ) := by
    change regular (Equiv.Perm (Boxes μ)) g.val ((v : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ)=_
    rw [hv]
  let L : S.toSubmodule →ₗ[ℂ] (Equiv.Perm (Boxes μ) → ℂ) :=
    (columnModule μ).toSubmodule.subtype.comp S.toSubmodule.subtype
  have hli : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp L
    change LinearIndependent ℂ (fun g => ((f g : (columnModule μ).toSubmodule) : Equiv.Perm (Boxes μ) → ℂ))
    simpa only [hmap] using rankVectors_independent μ
  exact hli.fintype_card_le_finrank

/- Entropy lower bound from Young vectors for the removed-diagram step of the
main induction. -/
lemma shape_dimension_entropy (μ : YoungDiagram) {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V)
    [τ.IsIrreducible] (hτ : hasShape μ (Equiv.refl _) τ)
    (L : ℕ) (hL : ∀ x : Boxes μ, x.val.1+x.val.2<L) :
    (Fintype.card (Boxes μ)).factorial ≤ L^(Fintype.card (Boxes μ))*Module.finrank ℂ V := by
  let f (x : Boxes μ) : Fin L := ⟨x.val.1+x.val.2,hL x⟩
  have he : colorStabilizer f=ranks μ := by
    ext g
    constructor
    · intro h x
      exact congrArg Fin.val (h x)
    · intro h x
      exact Fin.ext (h x)
  have hc:=card_perm_le_colors_mul_stabilizer f
  rw [he,Fintype.card_fin] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (rank_card_le_shape_finrank μ τ hτ))

end CoordinateSweeps.YoungCorner
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

namespace CoordinateSweeps.UnitaryIrrep

variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

lemma orbit_span_top (v : Fin ρ.dimension → ℂ) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun g => (ρ.matrix g).mulVec v)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun g => (ρ.matrix g).mulVec v))
  have hvS : v ∈ S := by
    have h := Submodule.subset_span (R := ℂ) (s := Set.range (fun g => (ρ.matrix g).mulVec v))
      (Set.mem_range_self (1 : Γ))
    simpa using h
  have hne : S ≠ ⊥ := by
    intro he; rw [he,Submodule.mem_bot] at hvS; exact hv hvS
  apply (ρ.irreducible S ?_).resolve_left hne
  intro g w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k,rfl⟩ := hw
    rw [Matrix.mulVec_mulVec,← map_mul]
    exact Submodule.subset_span (Set.mem_range_self (g*k))
  | zero => simp
  | add x y hx hy hix hiy => simpa only [Matrix.mulVec_add] using S.add_mem hix hiy
  | smul c x hx hi => simpa only [Matrix.mulVec_smul] using S.smul_mem c hi

/- Elementary irreducible dimension bound needed for the finite base case;
no partition classification has been assumed. -/
theorem dimension_le_card [Fintype Γ] : ρ.dimension ≤ Fintype.card Γ := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  obtain ⟨v,hv⟩ := exists_ne (0 : Fin ρ.dimension → ℂ)
  have h := finrank_le_of_span_eq_top (ρ.orbit_span_top v hv)
  simpa using h

lemma fixed_eq_bot_or_trivial : ρ.fixed = ⊥ ∨ ∀ g, ρ.matrix g = 1 := by
  have hi := ρ.irreducible ρ.fixed (by
    intro g v hv
    change ∀ k, (ρ.matrix k).mulVec ((ρ.matrix g).mulVec v)=(ρ.matrix g).mulVec v
    change ∀ k, (ρ.matrix k).mulVec v=v at hv
    rw [hv g]
    exact hv)
  rcases hi with h | h
  · exact Or.inl h
  · right
    intro g
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    have hv : v ∈ ρ.fixed := by rw [h]; trivial
    simpa using hv g

/- The exact zero of a uniform group average in every nontrivial irreducible.
This is the strict moment bound at z=0 used in06's b=1 base case. -/
theorem uniform_average_eq_zero [Fintype Γ]
    (hρ : ¬ ∀ g, ρ.matrix g=1) :
    (∑ g, (FiniteLaw.uniform Γ g : ℂ) • ρ.matrix g) = 0 := by
  have hfix : ρ.fixed = ⊥ := ρ.fixed_eq_bot_or_trivial.resolve_right hρ
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [Matrix.zero_mulVec]
  have hmem : (∑ g, (FiniteLaw.uniform Γ g : ℂ) • ρ.matrix g).mulVec v ∈ ρ.fixed := by
    intro k
    simp only [Matrix.sum_mulVec,Matrix.smul_mulVec,Matrix.mulVec_sum,Matrix.mulVec_smul,
      Matrix.mulVec_mulVec,← map_mul,FiniteLaw.uniform_apply]
    exact Equiv.sum_comp (Equiv.mulLeft k)
      (fun g => Complex.ofReal ((Fintype.card Γ : ℝ)⁻¹) • (ρ.matrix g).mulVec v)
  rwa [hfix,Submodule.mem_bot] at hmem

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.UnitaryIrrep

variable {Γ : Type*} [Group Γ] [Fintype Γ] (ρ : UnitaryIrrep Γ)

lemma sum_matrix_eq_zero (hρ : ¬ ∀ g, ρ.matrix g=1) : ∑ g, ρ.matrix g=0 := by
  have h := ρ.uniform_average_eq_zero hρ
  simp only [FiniteLaw.uniform_apply,← Finset.smul_sum] at h
  exact (smul_eq_zero.mp h).resolve_left (by
    simp [Fintype.card_ne_zero])

/- Uniform-in-the-irrep quantitative form of the finite one-block base
perturbation in06. A conditional coset has precisely these affine weights,
with u=1/m! and 0≤w≤1. No classification, finiteness of a chosen list of
representations, or continuity assumption is needed. -/
theorem affine_average_norm_le (hρ : ¬ ∀ g, ρ.matrix g=1)
    (u : ℝ) (hu : 0 < u) (w : Γ → ℝ)
    (hw : ∀ g, 0 ≤ w g) (hw1 : ∀ g, w g ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/2) :
    ‖((∑ g, ((1-z)*u+z*w g) : ℝ) : ℂ)⁻¹ •
       ∑ g, (((1-z)*u+z*w g : ℝ) : ℂ) • ρ.matrix g‖ ≤ 2*z/u := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  let Z : ℝ := ∑ g, ((1-z)*u+z*w g)
  have hN : (0 : ℝ) < Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  have hZ : (Fintype.card Γ : ℝ)*(u/2) ≤ Z := by
    calc
      _ = ∑ _ : Γ, u/2 := by simp
      _ ≤ Z := Finset.sum_le_sum (fun g _ => by
        have hh := mul_nonneg hz (hw g)
        nlinarith)
  have hZp : 0 < Z := lt_of_lt_of_le (mul_pos hN (by positivity)) hZ
  have hsum : (∑ g, (((1-z)*u+z*w g : ℝ) : ℂ) • ρ.matrix g) =
      (z : ℂ) • ∑ g, (w g : ℂ) • ρ.matrix g := by
    simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul,
      Finset.sum_add_distrib,← Finset.smul_sum,ρ.sum_matrix_eq_zero hρ,
      smul_zero,zero_add]
  have hn : ‖∑ g, (w g : ℂ) • ρ.matrix g‖ ≤ Fintype.card Γ := by
    calc
      _ ≤ ∑ g, ‖(w g : ℂ) • ρ.matrix g‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Γ, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro g _
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw g)]
        exact (mul_le_of_le_one_right (hw g)
          (matrix_unitary_norm_le _ (ρ.unitary g))).trans (hw1 g)
      _ = Fintype.card Γ := by simp
  change ‖(Z : ℂ)⁻¹ • _‖ ≤ _
  rw [hsum,norm_smul,norm_smul,norm_inv,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hZp,abs_of_nonneg hz]
  calc
    Z⁻¹ * (z * ‖∑ g, (w g : ℂ) • ρ.matrix g‖) ≤
        Z⁻¹ * (z * Fintype.card Γ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hz) (inv_nonneg.mpr hZp.le)
    _ ≤ 2*z/u := by
      rw [inv_mul_eq_div,div_le_iff₀ hZp]
      have hmult := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 2*z/u by positivity)
      have he : 2*z/u * ((Fintype.card Γ : ℝ)*(u/2)) = z*Fintype.card Γ := by
        field_simp
      rw [he] at hmult
      exact hmult

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.Grid

/- A one-coordinate grid, the base of06's induction. -/

lemma single_choiceWeight (d : ℕ) (z : ℝ) (ω : (single d).Choices) :
    (single d).choiceWeight z ω=
      (1-z)*(Fintype.card (Equiv.Perm (Cube d)) : ℝ)⁻¹+
        z*binaryLaw d (singleChoice d ω) := by
  unfold choiceWeight
  rw [Fin.prod_univ_one]
  rw [Fintype.prod_subsingleton _ (default : (single d).Line 0)]
  rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {d h : ℕ} (H : (Grid.single d).Holes h)

lemma single_probability (hf : H.Feasible) (z : ℝ) :
    H.probability z = ∑ g : H.stabilizer,
      (Grid.single d).choiceWeight z ((H.singleResidualEquiv hf).symm g).val :=
  ((H.singleResidualEquiv hf).symm.sum_comp _).symm

lemma single_conditionalAverage (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ρ =
      ((∑ g : H.stabilizer, (Grid.single d).choiceWeight z
        ((H.singleResidualEquiv hf).symm g).val : ℝ) : ℂ)⁻¹ •
      ∑ g : H.stabilizer, ((Grid.single d).choiceWeight z
        ((H.singleResidualEquiv hf).symm g).val : ℂ) • ρ.matrix g := by
  unfold conditionalAverage
  rw [H.single_probability hf z]
  congr 1
  rw [← (H.singleResidualEquiv hf).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro g _
  congr 2
  exact (H.singleResidualEquiv hf).apply_symm_apply g

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {d h : ℕ} (H : (Grid.single d).Holes h)

/- Actual conditioned single-coordinate operator, uniform in the hole family,
reference bijection, irrep, and representation realization. -/
theorem single_conditional_norm_le (hf : H.Feasible)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ¬ ∀ g, ρ.matrix g=1)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/2) :
    ‖H.conditionalAverage hf z ρ‖ ≤
      2*z*(Fintype.card (Equiv.Perm (Cube d)) : ℝ) := by
  rw [H.single_conditionalAverage hf z ρ]
  simp only [Grid.single_choiceWeight]
  simpa only [div_inv_eq_mul] using
    ρ.affine_average_norm_le hρ
      ((Fintype.card (Equiv.Perm (Cube d)) : ℝ)⁻¹)
      (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
      (fun g => binaryLaw d (Grid.singleChoice d ((H.singleResidualEquiv hf).symm g).val))
      (fun g => (binaryLaw d).nonneg _) (fun g => (binaryLaw d).mass_le_one _) hz hz1

lemma single_dimension_le (ρ : UnitaryIrrep H.stabilizer) :
    ρ.dimension ≤ Fintype.card (Equiv.Perm (Cube d)) := by
  apply ρ.dimension_le_card.trans
  have hc : Fintype.card H.stabilizer ≤ Fintype.card (Equiv.Perm (Grid.single d).Slot) :=
    Fintype.card_subtype_le _
  rwa [Fintype.card_congr (Equiv.permCongr (Grid.singleSlot d))] at hc

/- Exact one-block moment bound before choosing the absolute real interval. -/

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps

lemma e0_pos : 0 < e0 := by norm_num [e0,a]
lemma c0_eq_e0 : c0=e0 := rfl
lemma c0_small : 2*c0 < 1 := by norm_num [c0,a]

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

lemma logMoment_le_of_le {t u : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (htu : t ≤ u) :
    logMoment t ≤ (Real.log u : EReal) := by
  by_cases ht0 : t=0
  · simp [logMoment,ht0]
  · rw [logMoment,ite_eq_right ht0]
    exact_mod_cast (Real.log_le_log_iff (lt_of_le_of_ne ht (Ne.symm ht0)) hu).mpr htu

namespace Grid.Holes
variable {G : Grid} {h : ℕ} (H : G.Holes h)

/- Entire automatic branch06 eq16, with no representation type omitted. -/
theorem conditional_automatic (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : UnitaryIrrep H.stabilizer) (q : ℕ)
    (ha : (1+c G.size)*Real.log ρ.dimension ≤
      e G.size*h*Real.log G.size-H.cost) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost : ℝ) : EReal) := by
  apply (logMoment_le_of_le (H.conditionalMoment_nonneg hf z ρ q)
    (Nat.cast_pos.mpr ρ.positive) (H.conditionalMoment_le_dimension hf hz hz1 ρ q)).trans
  exact_mod_cast (show Real.log ρ.dimension ≤
    -c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost by nlinarith)

/- All one-dimensional types (trivial, sign, empty, and M=1), as required
explicitly in the statement and the first branch of the main induction. -/
theorem conditional_dimension_one {r : ℕ} (hr : ScaleLarge r) (hG : G.Allowed r)
    (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ρ.dimension=1) (q : ℕ) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost : ℝ) : EReal) := by
  apply H.conditional_automatic hf hz hz1 ρ q
  simpa [hρ] using H.allowance_nonneg hr hG

end Grid.Holes
end CoordinateSweeps

namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

lemma dimension_one_of_trivial (hρ : ∀ g, ρ.matrix g=1) : ρ.dimension=1 := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  obtain ⟨v,hv⟩ := exists_ne (0 : Fin ρ.dimension → ℂ)
  have hs := ρ.orbit_span_top v hv
  simp only [hρ,Matrix.one_mulVec,Set.range_const] at hs
  have hf := finrank_span_singleton (K := ℂ) hv
  rw [hs] at hf
  simpa using hf

end UnitaryIrrep

/- An explicit uniform base interval, so06's finiteness perturbation requires
no choice of a finite list of representation realizations. -/

lemma baseZeta_pos (r : ℕ) : 0 < baseZeta r := by
  have h := baseWidth_one_le r
  unfold baseZeta
  positivity

lemma single_card_le_baseWidth {r d : ℕ} (hd : d ≤ 2*r) :
    (Fintype.card (Equiv.Perm (Cube d)) : ℝ) ≤ baseWidth r := by
  simp only [Fintype.card_perm,Cube,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  unfold baseWidth
  exact_mod_cast Nat.factorial_le (Nat.pow_le_pow_right (by norm_num : 0 < 2) hd)

namespace Grid.Holes
variable {d h : ℕ} (H : (Grid.single d).Holes h)

theorem single_base_norm {r : ℕ} (hd : d ≤ 2*r) (hf : H.Feasible)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ρ.dimension ≠ 1)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r) :
    ‖H.conditionalAverage hf z ρ‖ ≤ (baseWidth r)⁻¹ := by
  have hB := baseWidth_one_le r
  have hc := single_card_le_baseWidth hd
  have hZ := baseZeta_pos r
  have hnt : ¬ ∀ g, ρ.matrix g=1 := fun hh => hρ (ρ.dimension_one_of_trivial hh)
  apply (H.single_conditional_norm_le hf ρ hnt hz
    (hz'.trans (baseZeta_le_half r))).trans
  calc
    2*z*(Fintype.card (Equiv.Perm (Cube d)) : ℝ) ≤ 2*baseZeta r*baseWidth r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz' (by norm_num)) hc
        (Nat.cast_nonneg _) (by positivity)
    _ ≤ (baseWidth r)⁻¹ := by
      unfold baseZeta
      field_simp
      nlinarith

/- A quantitative strict base estimate for all nontrivial irreducibles. -/
theorem single_base_moment {r : ℕ} (hd : d ≤ 2*r) (hf : H.Feasible)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ρ.dimension ≠ 1)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    {q : ℕ} (hq : 1 ≤ q) :
    schattenMoment q (H.conditionalAverage hf z ρ) ≤ (ρ.dimension : ℝ)⁻¹ := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  have hB := baseWidth_one_le r
  have hBp : 0 < baseWidth r := lt_of_lt_of_le (by norm_num) hB
  have hBi : (baseWidth r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hB
  have hD : (ρ.dimension : ℝ) ≤ baseWidth r :=
    (show (ρ.dimension : ℝ) ≤ (Fintype.card (Equiv.Perm (Cube d)) : ℝ) by
      exact_mod_cast H.single_dimension_le ρ).trans (single_card_le_baseWidth hd)
  have hnorm := H.single_base_norm hd hf ρ hρ hz hz'
  calc
    _ ≤ (ρ.dimension : ℝ)*‖H.conditionalAverage hf z ρ‖^(2*q) := trace_moment_le _ q
    _ ≤ baseWidth r*((baseWidth r)⁻¹)^(2*q) :=
      mul_le_mul hD (pow_le_pow_left₀ (norm_nonneg _) hnorm _)
        (by positivity) (by positivity)
    _ ≤ baseWidth r*((baseWidth r)⁻¹)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hBi (by omega)) hBp.le
    _ = (baseWidth r)⁻¹ := by field_simp
    _ ≤ (ρ.dimension : ℝ)⁻¹ := (inv_le_inv₀ hBp (by exact_mod_cast ρ.positive)).mpr hD

/- The full06 one-coordinate base with the manuscript's precise c,e and cost. -/
theorem single_conditional_main {r : ℕ} (hr : ScaleLarge r)
    (hG : (Grid.single d).Allowed r) (hf : H.Feasible)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    (ρ : UnitaryIrrep H.stabilizer) {q : ℕ} (hq : 1 ≤ q) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c (Grid.single d).size*Real.log ρ.dimension+
        e (Grid.single d).size*h*Real.log (Grid.single d).size-H.cost : ℝ) : EReal) := by
  have hz1 : z < 1 := lt_of_le_of_lt (hz'.trans (baseZeta_le_half r)) (by norm_num)
  by_cases hρ : ρ.dimension=1
  · exact H.conditional_dimension_one hr hG hf hz hz1 ρ hρ q
  have hm := H.single_base_moment (hG 0).2 hf ρ hρ hz hz' hq
  have hl := logMoment_le_of_le (H.conditionalMoment_nonneg hf z ρ q)
    (inv_pos.mpr (Nat.cast_pos.mpr ρ.positive)) hm
  rw [Real.log_inv] at hl
  apply hl.trans
  have hc : c (Grid.single d).size ≤ 1 :=
    (scale_coefficients hr _ hG).2.1.trans c0_small.le
  have hfnonneg : 0 ≤ Real.log ρ.dimension :=
    Real.log_nonneg (by exact_mod_cast ρ.positive)
  have ha := H.allowance_nonneg hr hG
  exact_mod_cast (show -Real.log ρ.dimension ≤
    -c (Grid.single d).size*Real.log ρ.dimension+
      e (Grid.single d).size*h*Real.log (Grid.single d).size-H.cost by nlinarith)

end Grid.Holes
end CoordinateSweeps

namespace CoordinateSweeps.Grid
lemma eq_single_of_b_one (G : Grid) (hb : G.b=1) : ∃ d, G=single d := by
  rcases G with ⟨b,hpos,bits⟩
  dsimp at hb
  subst b
  refine ⟨bits 0,?_⟩
  congr
  funext i
  exact congrArg bits (Subsingleton.elim i 0)

/- Full base branch for every allowed one-coordinate grid, not only a chosen
canonical coordinate presentation. -/
theorem conditional_main_b_one {r : ℕ} (hr : ScaleLarge r)
    (G : Grid) (hb : G.b=1) (hG : G.Allowed r)
    {h : ℕ} (H : G.Holes h) (hf : H.Feasible)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    (ρ : UnitaryIrrep H.stabilizer) {q : ℕ} (hq : 1 ≤ q) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost : ℝ) : EReal) := by
  obtain ⟨d,rfl⟩ := G.eq_single_of_b_one hb
  exact H.single_conditional_main hr hG hf hz hz' ρ hq
end CoordinateSweeps.Grid
end

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
/- The unswept free sites and the literal occupied junction board are
identified by the actual reference first-half sweep. -/
lemma initialJunction_conj (hf : H.Feasible) (g : H.stabilizer) :
    H.junctionFreeEquiv (H.junctionEquiv hf g)=
      (H.initialJunctionFree hf).permCongrHom (H.stabilizerFreeEquiv g) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl
lemma junctionChart_symm_boxes (hf : H.Feasible)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (g : Equiv.Perm (Fin (Fintype.card H.JunctionFree))) :
    (H.junctionChart hf eF).symm g=
      H.boxesChart μ eB ((eF.trans ((H.initialJunctionFree hf).symm.trans eB)).permCongrHom g) := by
  apply (H.junctionChart hf eF).injective
  rw [MulEquiv.apply_symm_apply]
  change g=eF.symm.permCongrHom (H.junctionFreeEquiv (H.junctionEquiv hf
    (H.boxesChart μ eB ((eF.trans ((H.initialJunctionFree hf).symm.trans eB)).permCongrHom g))))
  rw [H.initialJunction_conj]
  change g=eF.symm.permCongrHom ((H.initialJunctionFree hf).permCongrHom
    (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm (eB.symm.permCongrHom
      ((eF.trans ((H.initialJunctionFree hf).symm.trans eB)).permCongrHom g)))))
  rw [MulEquiv.apply_symm_apply]
  apply Equiv.ext
  intro x
  simp [Equiv.permCongrHom,Equiv.permCongr]
lemma junction_hasShape (hf : H.Feasible)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (σ : UnitaryIrrep H.stabilizer)
    (hσ : hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation) :
    hasShape μ (eF.trans ((H.initialJunctionFree hf).symm.trans eB))
      (σ.pullback (H.junctionChart hf eF).symm).asRepresentation := by
  let t := eF.trans ((H.initialJunctionFree hf).symm.trans eB)
  have he : (σ.pullback (H.junctionChart hf eF).symm).asRepresentation=
      (σ.pullback (H.boxesChart μ eB)).asRepresentation.comp t.permCongrHom := by
    apply MonoidHom.ext
    intro g
    change Matrix.toLinAlgEquiv' (σ.matrix ((H.junctionChart hf eF).symm g))=
      Matrix.toLinAlgEquiv' (σ.matrix (H.boxesChart μ eB (t.permCongrHom g)))
    rw [H.junctionChart_symm_boxes]
  rw [he]
  change hasShape μ t ((σ.pullback (H.boxesChart μ eB)).asRepresentation.comp t.permCongrHom)
  simpa only [Equiv.trans_refl] using (hasShape_reparam μ t (Equiv.refl _) _).mpr hσ
lemma conditionalAverage_cancelChart (hf : H.Feasible)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (σ : UnitaryIrrep H.stabilizer) (z : ℝ) :
    H.conditionalAverage hf z ((σ.pullback (H.junctionChart hf eF).symm).pullback (H.junctionChart hf eF))=
      H.conditionalAverage hf z σ := by
  rw [H.conditionalAverage_eq_sum,H.conditionalAverage_eq_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  change (_:ℂ) • σ.matrix ((H.junctionChart hf eF).symm (H.junctionChart hf eF (H.residual hf ω)))=_
  rw [MulEquiv.symm_apply_apply]
/- Exact hooked-main estimate for the actual stabilizer representation and
its literal initial-site Young labeling, with arbitrary feasible holes. -/
theorem actual_hook_bound (p : ℕ) (hp : 0<p) (hf : H.Feasible)
    (z : ℝ) (q : ℕ) (hq : 0<q) (c e : ℝ) (hc : 0 ≤ c) (hcq : c≤q)
    (s : ℕ) (hpS : p≤ s) (hAS : A.size≤ s) (hBS : B.size≤ s)
    (σ : UnitaryIrrep H.stabilizer)
    (hR : ∀ y : B.Slot, ∀ τ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z τ) ≤
        Real.exp (-c*Real.log τ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (hC : ∀ x : A.Slot, ∀ τ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z τ) ≤
        Real.exp (-c*Real.log τ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost))
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (hσ : hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation) (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c*Real.log σ.dimension+e*h*(Real.log A.size+Real.log B.size)-H.cost+c*h+
        (((2*q+1:ℕ):ℝ)*((A.size+B.size)*((2*p)*(2*p)):ℕ)+
          c*((A.size+B.size)*(41*p^2):ℕ))*Real.log (s+1:ℕ)) := by
  let eF := (Fintype.equivFin H.JunctionFree).symm
  have hh := H.grid_conditional_hook_bound p hp eF hf z q hq c e hc hcq s hpS hAS hBS
    (σ.pullback (H.junctionChart hf eF).symm) hR hC μ
    (eF.trans ((H.initialJunctionFree hf).symm.trans eB)) (H.junction_hasShape hf eF μ eB σ hσ) hhook
  rw [H.conditionalAverage_cancelChart] at hh
  exact hh
end CoordinateSweeps.Grid.Holes

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
namespace CoordinateSweeps
lemma moment_le_exp_of_logMoment_le {t B : ℝ} (ht : 0≤t)
    (h : logMoment t ≤ (B:EReal)) : t ≤ Real.exp B := by
  by_cases hz : t=0
  · rw [hz]; exact (Real.exp_pos _).le
  · rw [logMoment,ite_eq_right hz] at h
    have hh : Real.log t ≤ B := by exact_mod_cast h
    simpa only [Real.exp_log (lt_of_le_of_ne ht (Ne.symm hz))] using Real.exp_le_exp.mpr hh
end CoordinateSweeps
namespace CoordinateSweeps.Grid.Holes
open ScalarInduction YoungCorner
variable {A B : Grid} {r h q : ℕ} (H : (concat A B).Holes h)
theorem hook_auxiliary (hr : ScaleLarge r) (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) (hq : 1≤q)
    (hS : MainSizeReady q (concat A B).size)
    (z : ℝ) (hIA : MomentBound A q z) (hIB : MomentBound B q z)
    (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer)
    (p : ℕ) (hp : 0<p) (hpp : (p:ℝ)≤((concat A B).size:ℝ)^a)
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (hσ : hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation)
    (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-cHat (concat A B).size*Real.log σ.dimension+
        eHat (concat A B).size*h*Real.log (concat A B).size-H.cost+
          ((concat A B).size:ℝ)^((9:ℝ)/10)) := by
  let G := concat A B
  let L := Real.log G.size
  let cStar := c0+(11/10:ℝ)/Real.sqrt L
  let eStar := e0-(11/10:ℝ)/Real.sqrt L
  have hG : G.Allowed r := (concat_allowed A B r).mpr ⟨hA,hB⟩
  have hL : 0<L := (scale_coefficients hr G hG).1
  have hLA := (scale_coefficients hr A hA).1
  have hLB := (scale_coefficients hr B hB).1
  have hlogs := balanced_logs hA hB hAB hBA
  have hcsA : cStar ≤ c A.size ∧ e A.size≤eStar := improved_coefficients hL hLA hlogs.2.1
  have hcsB : cStar ≤ c B.size ∧ e B.size≤eStar := improved_coefficients hL hLB hlogs.2.2.2
  have hc : 0 ≤ cStar := by
    dsimp [cStar]
    have hc0 : 0 ≤ c0 := by norm_num [c0,a]
    positivity
  have hc2 : cStar≤2*c0 := hcsA.1.trans (scale_coefficients hr A hA).2.1
  have hcq : cStar≤q := hc2.trans ((by norm_num [c0,a] : 2*c0≤1).trans (by exact_mod_cast hq))
  have hR : ∀ y : B.Slot, ∀ τ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z τ) ≤
        Real.exp (-cStar*Real.log τ.dimension+eStar*H.rowCount y*Real.log A.size-(H.rowHoles y).cost) := by
    intro y τ
    apply (hIA _ _ _ τ).trans (Real.exp_le_exp.mpr ?_)
    have hF := Real.log_nonneg (show (1:ℝ)≤τ.dimension by exact_mod_cast τ.positive)
    have hc' := mul_le_mul_of_nonneg_right hcsA.1 hF
    have he' := mul_le_mul_of_nonneg_right hcsA.2
      (show 0≤(H.rowCount y:ℝ)*Real.log A.size by positivity)
    nlinarith
  have hC : ∀ x : A.Slot, ∀ τ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z τ) ≤
        Real.exp (-cStar*Real.log τ.dimension+eStar*H.columnCount x*Real.log B.size-(H.columnHoles x).cost) := by
    intro x τ
    apply (hIB _ _ _ τ).trans (Real.exp_le_exp.mpr ?_)
    have hF := Real.log_nonneg (show (1:ℝ)≤τ.dimension by exact_mod_cast τ.positive)
    have hc' := mul_le_mul_of_nonneg_right hcsB.1 hF
    have he' := mul_le_mul_of_nonneg_right hcsB.2
      (show 0≤(H.columnCount x:ℝ)*Real.log B.size by positivity)
    nlinarith
  have hs1 : (1:ℝ)<G.size := (Real.log_pos_iff (by exact_mod_cast G.size_pos.le)).mp hL
  have hpS : p≤G.size := by
    have hx : (G.size:ℝ)^a≤G.size := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hs1.le (show a≤1 by norm_num [a])
    exact_mod_cast hpp.trans hx
  have hAS : A.size≤G.size := by dsimp [G]; rw [concat_size]; nlinarith [A.size_pos,B.size_pos]
  have hBS : B.size≤G.size := by dsimp [G]; rw [concat_size]; nlinarith [A.size_pos,B.size_pos]
  have ht := H.actual_hook_bound p hp hf z q (by omega) cStar eStar hc hcq G.size hpS hAS hBS σ hR hC μ eB hσ hhook
  have hsizes := balanced_sizes hA hB hAB hBA
  have hErr := hook_error_bound hs1 q A.size B.size p cStar hc hc2 hsizes.2.1 hsizes.2.2.2 hpp
  have hroot : 2/e0≤Real.sqrt L := (Real.le_sqrt (by norm_num [e0,a]) hL.le).mpr
    (hr.2.1.trans (G.log_size_lower_one hG))
  have hgap := hook_strengthening hL hroot hc2
  have hcompare := hook_comparison (F:=Real.log σ.dimension) (h:=(h:ℝ)) (E:=
    (((2*q+1:ℕ):ℝ)*((A.size+B.size)*((2*p)*(2*p)):ℕ)+cStar*((A.size+B.size)*(41*p^2):ℕ))*Real.log (G.size+1:ℕ))
    hL (Real.log_nonneg (by exact_mod_cast σ.positive)) (Nat.cast_nonneg _) hgap.1 hgap.2
  have hlogsum : Real.log A.size+Real.log B.size=L := by
    dsimp [L,G]
    rw [concat_size,Nat.cast_mul,Real.log_mul (by exact_mod_cast A.size_pos.ne') (by exact_mod_cast B.size_pos.ne')]
  rw [hlogsum] at ht
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  have hES : _ ≤ (G.size:ℝ)^((9:ℝ)/10) := hErr.trans hS.hook
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul] at hcompare hES ⊢
  dsimp [cHat,eHat,c,e]
  change _ ≤ -(c0+1/Real.sqrt L+1/(20*Real.sqrt L))*Real.log σ.dimension+
    (e0-1/Real.sqrt L-1/(20*Real.sqrt L))*h*L-H.cost+(G.size:ℝ)^((9:ℝ)/10)
  dsimp [cStar,eStar] at *
  nlinarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.YoungCorner
lemma log_factorial_lower (k : ℕ) (hk : 0<k) :
    (k:ℝ)*Real.log k-k ≤ Real.log (k.factorial:ℝ) := by
  have hs := Stirling.le_log_factorial_stirling hk.ne'
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hl := Real.log_nonneg hk1
  have hp : 0≤Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith
lemma shape_finrank_pos (μ : YoungDiagram) :
    0 < Module.finrank ℂ (shapeSubrep μ (Equiv.refl _)).toSubmodule := by
  have : Nontrivial (shapeSubrep μ (Equiv.refl _)).toSubmodule :=
    by
      by_contra hn
      have : Subsingleton (shapeSubrep μ (Equiv.refl _)).toSubmodule := not_nontrivial_iff_subsingleton.mp hn
      apply bot_ne_top (α := Subrepresentation (shapeSubrep μ (Equiv.refl _)).toRepresentation)
      exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact Module.finrank_pos
/-- The translated removed diagram has the entropy required in the large-k
branch, using the checked factorial/rank-count lower bound. -/
lemma removed_dimension_entropy (μ : YoungDiagram) (p s : ℕ)
    (hs : 0 < s) (hM : Fintype.card (Boxes μ) ≤ s)
    (hfloor : (s:ℝ)^a ≤ p+1) (hL : 800 ≤ Real.log s)
    (hk : (s:ℝ)^(1-a/2) ≤ Fintype.card (Boxes (removedPart μ p))) :
    (a/4)*(Fintype.card (Boxes (removedPart μ p)):ℝ)*Real.log s ≤
      Real.log (Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule) := by
  let k := Fintype.card (Boxes (removedPart μ p))
  let D := Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule
  let L := 2*(Fintype.card (Boxes μ)/(p+1))
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs
  have hk0 : 0<k := by
    have hh : (0:ℝ)<k := (Real.rpow_pos_of_pos hs0 _).trans_le hk
    exact_mod_cast hh
  have hD0 : 0<D := shape_finrank_pos _
  have hLp : 0<L := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hk0
    exact Nat.zero_le (x.val.1+x.val.2) |>.trans_lt (removedPart_rank_lt μ p x)
  have hL0 : (0:ℝ)<L := by exact_mod_cast hLp
  have hc := shape_dimension_entropy (removedPart μ p)
    (shapeSubrep (removedPart μ p) (Equiv.refl _)).toRepresentation
    (shapeSubrep_hasShape _ _) L (removedPart_rank_lt μ p)
  have hc' : (k.factorial:ℝ) ≤ (L:ℝ)^k*D := by exact_mod_cast hc
  have hlog := Real.log_le_log (by exact_mod_cast Nat.factorial_pos k : (0:ℝ)<k.factorial) hc'
  rw [Real.log_mul (by positivity : (L:ℝ)^k≠0) (by exact_mod_cast hD0.ne'),Real.log_pow] at hlog
  have hfac := log_factorial_lower k hk0
  have hLp' : (L:ℝ)*(p+1) ≤ 2*s := by
    have hh := Nat.div_mul_le_self (Fintype.card (Boxes μ)) (p+1)
    have hh' : (Fintype.card (Boxes μ)/(p+1))*(p+1) ≤ s := hh.trans hM
    dsimp [L]
    exact_mod_cast (show 2*(Fintype.card (Boxes μ)/(p+1))*(p+1)≤2*s by nlinarith [hh'])
  have hLupper : (L:ℝ) ≤ 2*(s:ℝ)^(1-a) := by
    have hh := mul_le_mul_of_nonneg_left hfloor hL0.le
    have hhs : (L:ℝ)*(s:ℝ)^a ≤ 2*s := hh.trans hLp'
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hs0 a)).mp
    calc
      _ ≤ 2*(s:ℝ) := hhs
      _ = 2*(s:ℝ)^(1-a)*(s:ℝ)^a := by rw [mul_assoc,←Real.rpow_add hs0]; norm_num
  have hLogL : Real.log L ≤ Real.log 2+(1-a)*Real.log s := by
    have hh := Real.log_le_log hL0 hLupper
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hs0 _).ne',Real.log_rpow hs0] at hh
    exact hh
  have hLogk : (1-a/2)*Real.log s ≤ Real.log k := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hs0 (1-a/2)) hk
    simpa only [Real.log_rpow hs0] using hh
  have hl2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hkR : (0:ℝ)≤k := Nat.cast_nonneg _
  have hh1 := mul_le_mul_of_nonneg_left hLogL hkR
  have hh2 := mul_le_mul_of_nonneg_left hLogk hkR
  have hh3 : (a/4)*Real.log s ≥ Real.log 2+1 := by norm_num [a] at *; linarith
  have hh4 := mul_le_mul_of_nonneg_left hh3 hkR
  change (a/4)*(k:ℝ)*Real.log s ≤ Real.log D
  nlinarith
end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.Grid.Holes
open YoungCorner ScalarInduction
variable {G : Grid} {h : ℕ} (H : G.Holes h)
lemma exists_initial_shape (σ : UnitaryIrrep H.stabilizer) :
    ∃ (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ),
      hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation := by
  let τ := (σ.pullback H.stabilizerFreeEquiv.symm).asRepresentation
  obtain ⟨p,hp⟩ := exists_partitionShape τ
  refine ⟨diagramOfPartition p,partitionFilling p,?_⟩
  have hh : hasShape (V:=Fin σ.dimension → ℂ) (diagramOfPartition p)
      ((partitionFilling p).symm.trans (partitionFilling p))
      (τ.comp (partitionFilling p).symm.permCongrHom) :=
    (hasShape_reparam (diagramOfPartition p) (partitionFilling p).symm (partitionFilling p) τ).mpr hp
  change hasShape (V:=Fin σ.dimension → ℂ) (diagramOfPartition p) (Equiv.refl _)
    (τ.comp (partitionFilling p).symm.permCongrHom)
  simpa only [Equiv.symm_trans_self] using hh

lemma augmented_boxesChart (μ : YoungDiagram) (p : ℕ) (eB : H.FreeAt 0 ≃ Boxes μ)
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    (H.augmented x ω₀).boxesChart (hookPart μ p) (H.augmentedRetainedEquiv μ p eB x ω₀).symm=
      H.augmentedRetainedChart μ p eB x ω₀ := by
  rfl
lemma retained_log_dimension (μ : YoungDiagram) (p : ℕ) (eB : H.FreeAt 0 ≃ Boxes μ)
    (σ : UnitaryIrrep H.stabilizer)
    (ρ : UnitaryIrrep (H.placementChart (H.removedPlacement μ p eB)).stabilizer)
    (hd : σ.dimension≤(Fintype.card (Boxes μ))^(Fintype.card (Boxes (removedPart μ p)))*ρ.dimension) :
    Real.log σ.dimension≤Real.log ρ.dimension+
      Fintype.card (Boxes (removedPart μ p))*Real.log G.size := by
  have hM : Fintype.card (Boxes μ)≤G.size := by
    rw [←Fintype.card_congr eB,H.card_freeAt]
    exact Nat.sub_le _ _
  have hh := hd.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM _))
  have hhR : (σ.dimension:ℝ)≤(G.size:ℝ)^(Fintype.card (Boxes (removedPart μ p)))*ρ.dimension := by exact_mod_cast hh
  have hlog := Real.log_le_log (by exact_mod_cast σ.positive : (0:ℝ)<σ.dimension) hhR
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  rw [Real.log_mul (by positivity : (G.size:ℝ)^(Fintype.card (Boxes (removedPart μ p)))≠0)
    (by exact_mod_cast ρ.positive.ne'),Real.log_pow] at hlog
  linarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner ScalarInduction
variable {A B : Grid} {r h q : ℕ} (H : (concat A B).Holes h)
/-- Large-dimension branch of the exact main: actual retained constituent,
actual augmented paths, induced placement-cycle estimate, and absorbed entropy. -/
theorem conditional_large_main (hr : ScaleLarge r) (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) (hq : 1≤q)
    (hS : MainSizeReady q (concat A B).size)
    (z : ℝ) (hz : 0≤z) (hz' : z<1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g≤lineLaw ((concat A B).bits j) z hz hz'.le g)
    (hhi : ∀ j g, lineLaw ((concat A B).bits j) z hz hz'.le g≤2*FiniteLaw.uniform _ g)
    (hIA : MomentBound A q z) (hIB : MomentBound B q z)
    (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer)
    (hF : ((concat A B).size:ℝ)^(1-a/4)≤Real.log σ.dimension) :
    schattenMoment q (H.conditionalAverage hf z σ)≤
      Real.exp (-c (concat A B).size*Real.log σ.dimension+
        e (concat A B).size*h*Real.log (concat A B).size-H.cost) := by
  let G := concat A B
  let p := ⌊(G.size:ℝ)^a⌋₊
  let L := Real.log G.size
  obtain ⟨μ,eB,hσ⟩ := H.exists_initial_shape σ
  obtain ⟨ρ,hρ,hm,hd⟩ := H.exists_retained_irrep μ p eB σ hσ
  let k := Fintype.card (Boxes (removedPart μ p))
  let D := Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule
  have hG : G.Allowed r := (concat_allowed A B r).mpr ⟨hA,hB⟩
  have hcoeff := scale_coefficients hr G hG
  have hL : 0<L := hcoeff.1
  have hs : (1:ℝ)<G.size := (Real.log_pos_iff (by exact_mod_cast G.size_pos.le)).mp hL
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hp : 0<p := by
    change 1≤⌊(G.size:ℝ)^a⌋₊
    apply (Nat.one_le_floor_iff _).mpr
    exact Real.one_le_rpow hs.le (by norm_num [a])
  have hpp : (p:ℝ)≤(G.size:ℝ)^a := Nat.floor_le (Real.rpow_nonneg hs0.le _)
  have hfloor : (G.size:ℝ)^a≤p+1 := (Nat.lt_floor_add_one _).le
  let budget := -cHat G.size*Real.log ρ.dimension+eHat G.size*(h+k)*L+(G.size:ℝ)^((9:ℝ)/10)
  have hT : ∀ (x : H.Placement (k:=k)) (ω₀ : {ω : G.Choices // H.Compatible ω}),
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep (H.removedPlacement μ p eB) x ω₀ ρ))≤Real.exp (budget-(H.augmented x ω₀).cost) := by
    intro x ω₀
    have hsH := H.augmented_hasShape μ p eB ρ hρ x ω₀
    rw [←H.augmented_boxesChart] at hsH
    have hh := (H.augmented x ω₀).hook_auxiliary hr hA hB hAB hBA hq hS z hIA hIB
      (H.augmented_feasible x ω₀) (H.augmentedIrrep (H.removedPlacement μ p eB) x ω₀ ρ)
      p hp hpp (hookPart μ p) (H.augmentedRetainedEquiv μ p eB x ω₀).symm hsH (hookPart_property μ p)
    apply hh.trans_eq
    congr 1
    change -cHat (concat A B).size*Real.log ρ.dimension+
      eHat (concat A B).size*((h+k:ℕ):ℝ)*Real.log (concat A B).size-
      (H.augmented x ω₀).cost+((concat A B).size:ℝ)^((9:ℝ)/10)=budget-(H.augmented x ω₀).cost
    dsimp [budget,L,k,G]
    push_cast
    ring
  have hind := H.actual_induced_endgame hf (H.removedPlacement μ p eB) ρ σ hz hz' hlo hhi q (by omega) budget hT
  have hMoment0 := H.conditionalMoment_nonneg hf z σ q
  have hD0 : 0<D := shape_finrank_pos _
  have hD0R : (0:ℝ)<D := by exact_mod_cast hD0
  have hDT : (D:ℝ)*schattenMoment q (H.conditionalAverage hf z σ)≤Real.exp (budget-H.cost+Real.log 4*k*G.b) :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hMoment0).trans hind
  have ht : schattenMoment q (H.conditionalAverage hf z σ)≤
      Real.exp (budget-H.cost+Real.log 4*k*G.b-Real.log D) := by
    rw [Real.exp_sub,Real.exp_log hD0R]
    exact (le_div_iff₀ hD0R).mpr (by simpa only [mul_comm] using hDT)
  have hD := H.retained_log_dimension μ p eB σ ρ hd
  have hM : Fintype.card (Boxes μ)≤G.size := by
    rw [←Fintype.card_congr eB,H.card_freeAt]
    exact Nat.sub_le _ _
  have h800 : 800≤Real.log G.size := by
    have hh := hr.2.1.trans (G.log_size_lower_one hG)
    norm_num [e0,a] at hh
    linarith
  have hEnt : (G.size:ℝ)^(1-a/2)≤k → (a/4)*(k:ℝ)*L≤Real.log D := by
    intro hh
    exact removed_dimension_entropy μ p G.size G.size_pos hM hfloor h800 hh
  have hcost := removed_cost_bound hs (Nat.cast_nonneg k) (Nat.cast_nonneg G.b) hcoeff.2.2.2 hF
    (Real.log_nonneg (by exact_mod_cast hD0 : (1:ℝ)≤D)) hS hEnt
  have hscalar := removed_endgame L (Real.log σ.dimension) (Real.log ρ.dimension) (Real.log D)
    k h G.b H.cost G.size ((G.size:ℝ)^((9:ℝ)/10)) hL
    (Real.log_nonneg (by exact_mod_cast σ.positive)) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hD
    (Real.sqrt_pos.mpr hL) hcost
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  simpa only [budget,cHat,eHat,c,e,L] using hscalar
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
open Filter

/-- Strong induction on the literal ordered coordinate count; every child is
an actual conditioned row/column grid, not a surrogate representation law. -/
theorem all_grid_moment_oai {r : ℕ} (hr : ScaleLarge r) (hrS : SparseScalar.ScaleReady r)
    (hS : ∀ G : Grid, G.Allowed r → ScalarInduction.MainSizeReady SparseScalar.q G.size)
    {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar) :
    ∀ G : Grid, G.Allowed r → MomentBound G SparseScalar.q z := by
  have hzB : z≤baseZeta r := hz.2.trans hζ.2.1
  have hz1 : z<1 := lt_of_le_of_lt (hzB.trans (baseZeta_le_half r)) (by norm_num)
  have hq : 1≤SparseScalar.q := by norm_num [SparseScalar.q]
  have aux : ∀ n : ℕ, ∀ G : Grid, G.b=n → G.Allowed r → MomentBound G SparseScalar.q z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hb hG h H hf σ
      have hnonneg := H.conditionalMoment_nonneg hf z σ SparseScalar.q
      by_cases hone : G.b=1
      · exact moment_le_exp_of_logMoment_le hnonneg
          (Grid.conditional_main_b_one hr G hone hG H hf hz.1 hzB σ hq)
      by_cases hdim : σ.dimension=1
      · exact moment_le_exp_of_logMoment_le hnonneg
          (H.conditional_dimension_one hr hG hf hz.1 hz1 σ hdim SparseScalar.q)
      by_cases haut : (1+c G.size)*Real.log σ.dimension ≤ e G.size*h*Real.log G.size-H.cost
      · exact moment_le_exp_of_logMoment_le hnonneg
          (H.conditional_automatic hf hz.1 hz1 σ SparseScalar.q haut)
      by_cases hF : Real.log σ.dimension < (G.size:ℝ)^(1-a/4)
      · exact H.conditional_sparse_main hr hrS hG (hS G hG) hf hζ hz σ hdim haut hF
      have hlarge : (G.size:ℝ)^(1-a/4)≤Real.log σ.dimension := le_of_not_gt hF
      have hb2 : 2≤G.b := by have hh:=G.positive; omega
      obtain ⟨A,B,hAB,hA,hB,hab,hba⟩ := G.exists_half_concat hb2
      have hallowed : A.Allowed r ∧ B.Allowed r :=
        (Grid.concat_allowed A B r).mp (by simpa only [hAB] using hG)
      have hIA : MomentBound A SparseScalar.q z := ih A.b (by omega) A rfl hallowed.1
      have hIB : MomentBound B SparseScalar.q z := ih B.b (by omega) B rfl hallowed.2
      subst G
      exact H.conditional_large_main hr hallowed.1 hallowed.2 hab hba hq
        (hS _ hG) z hz.1 hz1
        (fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).1)
        (fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).2)
        hIA hIB hf σ hlarge
  exact fun G hG => aux G.b G rfl hG

end CoordinateSweeps

end OAI
end

theorem solution : type_of% @OAI.CoordinateSweeps.all_grid_moment_oai := @OAI.CoordinateSweeps.all_grid_moment_oai
