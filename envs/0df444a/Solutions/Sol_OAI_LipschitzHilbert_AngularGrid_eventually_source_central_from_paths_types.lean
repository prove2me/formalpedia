-- Prove2me | solution 1 for OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T19:53:37.335084+00:00
-- url     : https://prove2.me/submissions/f11166e5-34d5-41a0-9295-75f51cad3423

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

omit [Fintype ι] in
theorem phaseParameter_range {D : ℝ} (hD : 1 ≤ D) :
    0 < phaseConstant / Real.log (2 * D) ∧
      phaseConstant / Real.log (2 * D) ≤ 1 / 3 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * D) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < Real.log (2 * D) := by linarith
  refine ⟨div_pos phaseConstant_pos hpos, (div_le_iff₀ hpos).2 ?_⟩
  have hc : phaseConstant ≤ (1 / 6 : ℝ) := by norm_num [phaseConstant]
  linarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SimplexTubeInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded analytic tubes preserve a common bound under finite convex
combinations of their real parameters. This is the scalar interpolation
step used for the finitely many shift parameters in manuscript §11. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*}

theorem phaseTubeLine_re_im (a b eta : ι → ℝ) (z : ℂ) :
    phaseTubeLine a b eta z = phaseTubePoint ((1-z.re) • a+z.re • b)
      (fun i => eta i+z.im*(b i-a i)) := by
  funext i
  apply Complex.ext
  · simp [phaseTubeLine,phaseTubePoint,Complex.mul_re,Complex.mul_im]
  · simp [phaseTubeLine,phaseTubePoint,Complex.mul_re,Complex.mul_im]
    ring

theorem convex_phaseTubeBound (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (C : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, phaseTubeBound F M a) :
    Convex ℝ {a | a ∈ D ∧ phaseTubeBound F C a} := by
  intro a ha b hb r s hr hs hrs
  refine ⟨hD ha.1 hb.1 hr hs hrs,?_⟩
  intro eta
  let f := fun z => F (phaseTubeLine a b eta z)
  obtain ⟨M,hM⟩ := hbounded
  have hfB : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨M,?_⟩
    rintro y ⟨z,hz,rfl⟩
    change ‖F (phaseTubeLine a b eta z)‖ ≤ M
    rw [phaseTubeLine_re_im]
    exact hM _ (hD ha.1 hb.1 (sub_nonneg.mpr hz.2) hz.1 (by ring)) _
  have hf0 : ∀ z ∈ Complex.re ⁻¹' {0}, ‖f z‖ ≤ C := by
    intro z hz
    change z.re = 0 at hz
    dsimp only [f]
    rw [phaseTubeLine_re_im]
    simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using
      ha.2 (fun i => eta i+z.im*(b i-a i))
  have hf1 : ∀ z ∈ Complex.re ⁻¹' {1}, ‖f z‖ ≤ C := by
    intro z hz
    change z.re = 1 at hz
    dsimp only [f]
    rw [phaseTubeLine_re_im]
    simpa only [hz,sub_self,zero_smul,one_smul,zero_add] using
      hb.2 (fun i => eta i+z.im*(b i-a i))
  have hs1 : s ≤ 1 := by linarith
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    f (z := (s:ℂ)) ⟨hs,hs1⟩ (hentire a ha.1 b hb.1 eta).diffContOnCl hfB hf0 hf1
  have hpower : C^(1-s)*C^s = C := by
    rw [← Real.rpow_add hC,sub_add_cancel,Real.rpow_one]
  have hr' : r = 1-s := by linarith
  simpa only [f,phaseTubeLine_re_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    add_zero,hpower,hr'] using h

theorem phaseTubeBound_finite_convex_combination (F : (ι → ℂ) → ℂ)
    (D : Set (ι → ℝ)) (hD : Convex ℝ D) (C : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, phaseTubeBound F M a)
    (S : Finset κ) (w : κ → ℝ) (v : κ → ι → ℝ)
    (hw : ∀ k ∈ S, 0 ≤ w k) (hsum : ∑ k ∈ S, w k = 1)
    (hv : ∀ k ∈ S, v k ∈ D) (hvertex : ∀ k ∈ S, phaseTubeBound F C (v k)) :
    phaseTubeBound F C (∑ k ∈ S, w k • v k) := by
  have hc := convex_phaseTubeBound F D hD C hC hentire hbounded
  exact (hc.sum_mem hw hsum (fun k hk => ⟨hv k hk,hvertex k hk⟩)).2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SimplexBarycenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shift-simplex vertices give the identical bound at the diagonal
parameter μ/K. The estimate has no factor depending on the number of shifts. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem phaseTubeBound_barycenter (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (C mu : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, phaseTubeBound F M a)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι, phaseTubeBound F C (Pi.single i mu)) :
    phaseTubeBound F C (fun _ => mu/(Fintype.card ι:ℝ)) := by
  have hcard : (Fintype.card ι:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := ι)
  have hsum : ∑ _i : ι, (1/(Fintype.card ι:ℝ)) = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have hmean : (∑ i : ι, (1/(Fintype.card ι:ℝ)) • Pi.single i mu) =
      fun _ => mu/(Fintype.card ι:ℝ) := by
    funext j
    simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply,mul_ite,
      div_eq_mul_inv,mul_comm]
  rw [← hmean]
  exact phaseTubeBound_finite_convex_combination F D hD C hC hentire hbounded Finset.univ
    (fun _ => 1/(Fintype.card ι:ℝ)) (fun i => Pi.single i mu)
    (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)) hsum
    (fun i _ => hvertices i) (fun i _ => hvertex i)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_HierarchyVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-root logarithmic variation bound for shifted angular blocks. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem sum_log_ratios (n : ℕ → ℝ) (N : ℕ) (hn : ∀ j ≤ N, 0 < n j) :
    (∑ j ∈ Finset.range N, Real.log (n j / n (j + 1))) = Real.log (n 0 / n N) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      Real.log (n j / n (j + 1)) = Real.log (n j) - Real.log (n (j + 1)) :=
    Real.log_div (hn j (by have := Finset.mem_range.mp hj; omega)).ne'
      (hn (j + 1) (by have := Finset.mem_range.mp hj; omega)).ne'
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  exact (Real.log_div (hn 0 (Nat.zero_le N)).ne' (hn N le_rfl).ne').symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppedScalarExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite scalar algebra for a stopped path. The terminal coefficient is
retained, so a small positive terminal mass is never replaced by zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

/-- Unroll up to the first inactive index, keeping its exact terminal value. -/
theorem stoppedScalarExpansion_eq (active : ℕ → Prop) (beta terminal : ℕ → ℝ)
    (count stop j : ℕ) (hstop : stop ≤ count)
    (ha : ∀ i < stop, active (j+i)) (hz : ¬active (j+stop)) :
    stoppedScalarExpansion active beta terminal count j =
      terminal (j+stop)*∏ i ∈ Finset.range stop, beta (j+i) := by
  induction stop generalizing count j with
  | zero =>
    have hz' : ¬active j := by simpa only [Nat.add_zero] using hz
    cases count <;> simp [stoppedScalarExpansion,hz']
  | succ stop ih =>
    cases count with
    | zero => omega
    | succ count =>
      have hactive : active j := by simpa using ha 0 (by omega)
      rw [stoppedScalarExpansion,ite_eq_left hactive]
      have ha' : ∀ i < stop, active ((j+1)+i) := by
        intro i hi
        simpa only [Nat.add_assoc,Nat.add_comm 1 i] using ha (i+1) (by omega)
      have hz' : ¬active ((j+1)+stop) := by
        simpa only [Nat.add_assoc,Nat.add_comm 1 stop] using hz
      rw [ih count (j+1) (by omega) ha' hz',Finset.prod_range_succ']
      have heq : (∏ i ∈ Finset.range stop, beta (j+(i+1))) =
          ∏ i ∈ Finset.range stop, beta (j+1+i) := by
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        omega
      rw [heq]
      have hj : j+(stop+1) = j+1+stop := by omega
      rw [hj]
      simp only [Nat.add_zero]
      ring

/-- A normalized path reaches its final parent with probability at most
one. This is the scalar form of the subunit child transition bound. -/
theorem normalized_path_parent_bound (V D : ℕ → ℝ) (N : ℕ)
    (hV : ∀ j ≤ N, 0 < V j) (hD : ∀ j ≤ N, 0 < D j)
    (hchild : ∀ j < N, V (j+1) ≤ D j) :
    (∏ j ∈ Finset.range (N+1), V j/D j) ≤ V 0/D N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun j hj => hV j (by omega))
      (fun j hj => hD j (by omega)) (fun j hj => hchild j (by omega))
    rw [Finset.prod_range_succ]
    calc
      _ ≤ (V 0/D N)*(V (N+1)/D (N+1)) :=
        mul_le_mul_of_nonneg_right hprev (div_nonneg (hV (N+1) (by omega)).le (hD (N+1) le_rfl).le)
      _ = (V 0/D (N+1))*(V (N+1)/D N) := by ring
      _ ≤ V 0/D (N+1) := mul_le_of_le_one_right
        (div_nonneg (hV 0 (by omega)).le (hD (N+1) le_rfl).le)
        ((div_le_one (hD N (by omega))).mpr (hchild N (by omega)))

/-- An arbitrary terminal coefficient with a weight bound gives the
required per-top probability bound, with no depth factor. -/
theorem normalized_terminal_weight_bound (V D : ℕ → ℝ) (N : ℕ)
    (e C w : ℝ) (hV : ∀ j ≤ N, 0 < V j) (hD : ∀ j ≤ N, 0 < D j)
    (hchild : ∀ j < N, V (j+1) ≤ D j) (he : 0 ≤ e) (hCw : e ≤ C*w)
    (hfinal : 1 ≤ D N) :
    e*(∏ j ∈ Finset.range (N+1), V j/D j)/V 0 ≤ C*w := by
  have hp := normalized_path_parent_bound V D N hV hD hchild
  calc
    _ ≤ e*(V 0/D N)/V 0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp he) (hV 0 (by omega)).le
    _ = e/D N := by field_simp [(hV 0 (by omega)).ne']
    _ ≤ e := div_le_self he hfinal
    _ ≤ C*w := hCw

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_VertexIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrating the vertex amount

The actual finite terminal flow gives pointwise good-path domination on the
large-mass region. Integrating that domination together with the
small-mass estimate extracts the normalized vertex energy from its
nonnegative amount. This is the finite nonnegative assembly in §11.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ ι : Type*} [MeasurableSpace α] [Fintype κ] [Fintype ι] {N : ℕ}

attribute [local instance] Classical.propDecidable

section Energy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace α] [Fintype κ] [Fintype ι] in
theorem normalized_vertex_energy_eq {n a p : ℝ} (hn : 0 < n) (hp : p ≠ 0) (A : E) :
    ‖(n ^ (a / p - 1)) • A‖ ^ p = n ^ (a - p) * ‖A‖ ^ p := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn.le _),
    Real.mul_rpow (Real.rpow_nonneg hn.le _) (norm_nonneg _), ← Real.rpow_mul hn.le]
  have heq : (a / p - 1) * p = a - p := by
    have h := div_mul_cancel₀ a hp
    nlinarith
  rw [heq]

omit [Fintype κ] [Fintype ι] in
/-- Subtracting the integrable mass baseline extracts the normalized energy
without any extra domination or measurability assumption on that energy. -/
theorem normalized_vertex_energy_integrable (μ : Measure α)
    (n : α → ℝ) (A : α → E) {a p : ℝ} (hn : ∀ x, 0 < n x) (hp : p ≠ 0)
    (hnint : Integrable n μ) (hVint : Integrable (fun x => vertexAmount (n x) (A x) a p) μ) :
    Integrable (fun x => ‖(n x ^ (a / p - 1)) • A x‖ ^ p) μ := by
  have heq : (fun x => ‖(n x ^ (a / p - 1)) • A x‖ ^ p) =
      fun x => vertexAmount (n x) (A x) a p - n x := by
    funext x
    rw [normalized_vertex_energy_eq (hn x) hp]
    unfold vertexAmount
    ring
  rw [heq]
  exact hVint.sub hnint

omit [Fintype κ] [Fintype ι] in
/-- An integrated amount bound gives the desired vertex Lp energy bound. -/
theorem normalized_vertex_moment_le (μ : Measure α)
    (n : α → ℝ) (A : α → E) {a p T : ℝ} (hn : ∀ x, 0 < n x) (hp : 0 < p)
    (hnint : Integrable n μ) (hVint : Integrable (fun x => vertexAmount (n x) (A x) a p) μ)
    (hbound : (∫ x, vertexAmount (n x) (A x) a p ∂μ) ≤ T) :
    (∫ x, ‖(n x ^ (a / p - 1)) • A x‖ ^ p ∂μ) ^ (1 / p) ≤ T ^ (1 / p) := by
  have henergy := normalized_vertex_energy_integrable μ n A hn hp.ne' hnint hVint
  have hle : (∫ x, ‖(n x ^ (a / p - 1)) • A x‖ ^ p ∂μ) ≤ T := by
    apply (integral_mono henergy hVint _).trans hbound
    intro x
    change ‖(n x ^ (a / p - 1)) • A x‖ ^ p ≤ vertexAmount (n x) (A x) a p
    rw [normalized_vertex_energy_eq (hn x) hp.ne']
    exact le_add_of_nonneg_left (hn x).le
  exact Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    hle (one_div_nonneg.mpr hp.le)

end Energy

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unary residual energies

The amount is the actual `vertexAmount` from §11. Its logarithmic motion
and the small correction `log(1+h/V)` are the analytic ingredients of
the unary-segment telescope in §10, equation `src-28`.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem vertexAmount_pos {n a p : ℝ} (hn : 0 < n) (A : E) :
    0 < vertexAmount n A a p := by
  unfold vertexAmount
  positivity

omit [NormedSpace ℝ E] in
theorem mass_le_vertexAmount {n a p : ℝ} (hn : 0 ≤ n) (A : E) :
    n ≤ vertexAmount n A a p := by
  unfold vertexAmount
  exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg (norm_nonneg A) _))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCountParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dyadic source parameters meet the counting hypotheses. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem blockCount_pos {L : ℝ} (hL : 1 < L) : 0 < blockCount L := by
  apply Nat.one_le_ceil_iff.mpr
  exact sq_pos_of_pos (Real.log_pos hL)

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated nested angular grids and their actual eligible-top masses. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace AngularGrid

theorem index_parent (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.index (level + 1) slope / (g.branching : ℤ) = g.index level slope := by
  have hG : g.branching ≠ 0 := by have h := g.branching_ge_two; omega
  simpa only [index, pow_succ, mul_assoc] using
    (Int.mul_natCast_floor_div_cancel hG
      (((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level))

variable {ι X : Type*}

theorem cellTops_subset_parent (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (level : ℕ) (child : ℤ) :
    g.cellTops tops slope precision cutoff (level + 1) child ⊆
      g.cellTops tops slope precision cutoff level (child / (g.branching : ℤ)) := by
  intro i hi
  obtain ⟨hit, hindex, heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  apply (g.mem_cellTops _ _ _ _ _ _ _).2
  refine ⟨hit, ?_, g.eligible_parent (hp i hit) level heligible⟩
  rw [← g.index_parent level (slope i), hindex]

theorem mass_nonnegative (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    0 ≤ g.mass tops slope precision cutoff weight level cell x :=
  Finset.sum_nonneg fun i _ => hw i x

theorem mass_pos_of_member (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (cell : ℤ) (x : X) {i : ι}
    (hi : i ∈ g.cellTops tops slope precision cutoff level cell) :
    0 < g.mass tops slope precision cutoff weight level cell x := by
  classical
  exact (hw i x).trans_le (Finset.single_le_sum (fun j _ => (hw j x).le) hi)

/-- An eligible top supplies a strictly positive summand on its own path. -/
theorem path_mass_pos (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (top : ι) (htop : top ∈ tops) (heligible : g.eligible cutoff (precision top) level)
    (x : X) : 0 < g.mass tops slope precision cutoff weight level (g.index level (slope top)) x :=
  g.mass_pos_of_member tops slope precision cutoff weight hw level _ x
    ((g.mem_cellTops _ _ _ _ _ _ _).2 ⟨htop, rfl, heligible⟩)

/-- Every angular mass is a submass of the fixed total top weight. -/
theorem mass_le_total (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight level cell x ≤ ∑ i ∈ tops, weight i x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro i _ _
    exact hw i x

/-- Child mass is at most parent mass, with the eligibility restriction
already built into both finite sums. -/
theorem mass_le_parent (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (level : ℕ) (child : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) child x ≤
      g.mass tops slope precision cutoff weight level (child / (g.branching : ℤ)) x := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (g.cellTops_subset_parent tops slope precision cutoff hp level child) (fun i _ _ => hw i x)

/-- Along any fixed top's angular path the actual mass is antitone. -/
theorem path_mass_antitone (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (top : ι) (x : X) :
    Antitone fun level => g.mass tops slope precision cutoff weight level (g.index level (slope top)) x := by
  apply antitone_nat_of_succ_le
  intro level
  simpa only [g.index_parent] using
    g.mass_le_parent tops slope precision cutoff weight hp hw level (g.index (level + 1) (slope top)) x

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses formed from actual top sets in a common angular ancestor. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_eq_of_add (g : AngularGrid) (base steps : ℕ) {s t : ℝ}
    (h : g.index (base + steps) s = g.index (base + steps) t) :
    g.index base s = g.index base t := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    rw [← g.index_parent (base + steps) s, ← g.index_parent (base + steps) t]
    simpa only [Nat.add_succ] using congrArg (fun a : ℤ => a / g.branching) h

theorem index_eq_of_le (g : AngularGrid) {base level : ℕ} (hle : base ≤ level)
    {s t : ℝ} (h : g.index level s = g.index level t) :
    g.index base s = g.index base t := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.index_eq_of_add base steps h

/-- Tops in a descendant cell remain eligible and lie in its actual ancestor. -/
theorem cellTops_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  intro i hi
  obtain ⟨hit, hindex, he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  exact (g.mem_cellTops _ _ _ _ _ _ _).2
    ⟨hit, g.index_eq_of_le hle hindex, g.eligible_of_le (hp i hit) hle he⟩

theorem parent_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  exact Finset.subset_union_left

theorem boundary_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) :
    g.boundaryTops tops slope precision cutoff base level gap s ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  classical
  apply Finset.union_subset
  · exact g.cellTops_subset_ancestor tops slope precision cutoff hp hle s
  · exact Finset.filter_subset _ _

/-- The immediate child, parent, boundary and block ancestor have ordered masses. -/
theorem boundary_mass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) (g.index (level + 1) s) x ≤
        g.mass tops slope precision cutoff weight level (g.index level s) x ∧
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
        g.boundaryMass tops slope precision cutoff weight base level gap s x ∧
    g.boundaryMass tops slope precision cutoff weight base level gap s x ≤
        g.mass tops slope precision cutoff weight base (g.index base s) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := g.mass_le_parent tops slope precision cutoff weight hp hw level
      (g.index (level + 1) s) x
    simpa only [g.index_parent] using h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.parent_subset_boundary tops slope precision cutoff base level gap s)
      (fun i _ _ => hw i x)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.boundary_subset_ancestor tops slope precision cutoff hp hle gap s)
      (fun i _ _ => hw i x)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularAnalyticWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic transition weights for the shared angular packet family.
The exact modulus is the child-to-boundary mass ratio raised to the
real part of the corresponding complex parameter. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem analyticTransition_norm (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell) :
    ‖analyticTransition mass boundary phase level cell‖ =
      (mass (level + 1) cell / boundary level cell) ^ (phase level).re := by
  rw [analyticTransition, Complex.norm_exp, Real.rpow_def_of_pos (div_pos hm hb)]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem analyticTransition_norm_le_one (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell)
    (hle : mass (level + 1) cell ≤ boundary level cell) (hphase : 0 ≤ (phase level).re) :
    ‖analyticTransition mass boundary phase level cell‖ ≤ 1 := by
  rw [analyticTransition_norm mass boundary phase level cell hm hb]
  exact Real.rpow_le_one (div_nonneg hm.le hb.le) ((div_le_one hb).mpr hle) hphase

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses and logarithmic variation along actual eligible top
paths. Every boundary uses the start of the block whose last transition
is the current level, in the shared family of all shifted groupings. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_center (g : AngularGrid) (level : ℕ) (cell : ℤ) :
    g.index level (g.center level cell) = cell := by
  have hG : (g.branching : ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((g.center level cell - g.origin) / g.rootWidth) *
      (g.branching : ℝ)^level = (cell : ℝ) + 1/2 := by
    unfold center left width
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
    ring
  unfold index
  rw [heq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem boundaryTops_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) {base level : ℕ} (hle : base ≤ level)
    (gap : ℝ) {s t : ℝ} (hc : g.index (level+1) s = g.index (level+1) t) :
    g.boundaryTops tops slope precision cutoff base level gap s =
      g.boundaryTops tops slope precision cutoff base level gap t := by
  have hp := g.index_eq_of_le (Nat.le_succ level) hc
  have ha := g.index_eq_of_le (hle.trans (Nat.le_succ level)) hc
  simp only [boundaryTops, outsideNearTops, hp, ha, hc]

theorem boundaryMass_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {base level : ℕ} (hle : base ≤ level) (gap : ℝ) {s t : ℝ}
    (hc : g.index (level+1) s = g.index (level+1) t) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.boundaryMass tops slope precision cutoff weight base level gap t x := by
  unfold boundaryMass
  rw [g.boundaryTops_eq_of_cell tops slope precision cutoff hle gap hc]

theorem sourceBoundaryMass_path (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x =
      g.boundaryMass tops slope precision cutoff weight (level+1-K) level (gap level) s x := by
  apply g.boundaryMass_eq_of_cell tops slope precision cutoff weight (by omega)
  exact g.index_center (level+1) _

theorem sourceBoundaryMass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level+1) (g.index (level+1) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ≤
      g.mass tops slope precision cutoff weight (level+1-K) (g.index (level+1-K) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  have h := g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x
  exact ⟨h.1.trans h.2.1, h.2.2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularPathNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The equal-coordinate value of the shared analytic family. The
endpoint mass cancels exactly and leaves only parent-to-boundary ratios. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- The path product in the shared analytic family is the exponential
weight used in the full-root variation estimate. -/
theorem hierarchyWeight_eq_path_product (n b : ℕ → ℝ) (phase : ℕ → ℂ)
    (a : ℝ) (N : ℕ) (hn : 0 < n N)
    (hn' : ∀ j < N, 0 < n (j+1)) (hb : ∀ j < N, 0 < b j) :
    hierarchyWeight n (fun j => Real.log (b j / n (j+1))) phase a N =
      ((n N ^ (-a) : ℝ) : ℂ) * ∏ j ∈ Finset.range N,
        Complex.exp (phase j * (Real.log (n (j+1) / b j) : ℂ)) := by
  have hpow : ((n N ^ (-a) : ℝ) : ℂ) =
      Complex.exp ((-a * Real.log (n N) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hn, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.exp_sum, ← Complex.exp_add, hierarchyWeight, hierarchyLog]
  congr 1
  have hsum : (∑ j ∈ Finset.range N, phase j * (Real.log (n (j+1) / b j) : ℂ)) =
      -(∑ j ∈ Finset.range N, phase j * (Real.log (b j / n (j+1)) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN := Finset.mem_range.mp hj
    rw [Real.log_div (hn' j hjN).ne' (hb j hjN).ne',
      Real.log_div (hb j hjN).ne' (hn' j hjN).ne']
    push_cast
    ring
  rw [hsum]
  ring

theorem normalized_endpoint_telescope (n b : ℕ → ℝ) (a : ℝ) (N : ℕ)
    (hn : ∀ j ≤ N, 0 < n j) (hb : ∀ j < N, 0 < b j) :
    ((n 0 ^ a : ℝ) : ℂ) *
        hierarchyWeight n (fun j => Real.log (b j / n (j+1))) (fun _ => (a : ℂ)) a N =
      ((∏ j ∈ Finset.range N, (n j / b j)^a : ℝ) : ℂ) := by
  have hlogs : (∑ j ∈ Finset.range N, Real.log (n j / b j)) =
      Real.log (n 0 / n N) - ∑ j ∈ Finset.range N, Real.log (b j / n (j+1)) := by
    rw [← sum_log_ratios n N hn, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN := Finset.mem_range.mp hj
    rw [Real.log_div (hn j (by omega)).ne' (hb j hjN).ne',
      Real.log_div (hn j (by omega)).ne' (hn (j+1) (by omega)).ne',
      Real.log_div (hb j hjN).ne' (hn (j+1) (by omega)).ne']
    ring
  have hleft : ((n 0 ^ a : ℝ) : ℂ) = Complex.exp ((a * Real.log (n 0) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos (hn 0 (Nat.zero_le N)), Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      ((n j / b j)^a : ℝ) = Real.exp (a * Real.log (n j / b j)) := by
    rw [Real.rpow_def_of_pos (div_pos (hn j (by have := Finset.mem_range.mp hj; omega))
      (hb j (Finset.mem_range.mp hj)))]
    congr 1
    ring
  rw [hleft, hierarchyWeight, ← Complex.exp_add]
  rw [Finset.prod_congr rfl hterm, ← Real.exp_sum, Complex.ofReal_exp]
  congr 1
  unfold hierarchyLog
  have hscalar : a * Real.log (n 0) +
      (-a * Real.log (n N) - ∑ j ∈ Finset.range N, a * Real.log (b j / n (j+1))) =
        ∑ j ∈ Finset.range N, a * Real.log (n j / b j) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hlogs,
      Real.log_div (hn 0 (Nat.zero_le N)).ne' (hn N le_rfl).ne']
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hscalar
  push_cast at hc ⊢
  exact hc

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared source amplitude uses the packet's stopping mass and the
actual boundary mass at each transition. The assigned top supplies the
positive mass required by every logarithm along the packet's path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

theorem sourceTransition_norm_le_one (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (x : X) (level : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (level+1)) (hz : 0 ≤ (phase level).re) :
    ‖g.sourceTransition tops slope precision cutoff weight K gap phase x level
      (g.index (level+1) (slope top))‖ ≤ 1 := by
  have hn := g.path_mass_pos tops slope precision cutoff weight hw (level+1) top htop he x
  have hb := (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) hK gap level (slope top) x).1
  exact analyticTransition_norm_le_one _ _ phase level _ hn (hn.trans_le hb) hb hz

/-- At equal real coordinates the packet coefficient is precisely the
product of the parent-to-boundary ratios from the manuscript. -/
theorem source_normalized_endpoint (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : ι)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
    let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight
      K gap j (g.index (j+1) (slope top)) x
    ((n 0^a : ℝ) : ℂ) * (((n N^(-a) : ℝ) : ℂ) *
      g.packetPathProduct
        (g.sourceTransition tops slope precision cutoff weight K gap (fun _ => (a : ℂ)) x)
        0 N (slope top)) = ((∏ j ∈ Finset.range N, (n j / b j)^a : ℝ) : ℂ) := by
  dsimp only
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight
    K gap j (g.index (j+1) (slope top)) x
  have hn (j : ℕ) (hj : j ≤ N) : 0 < n j :=
    g.path_mass_pos tops slope precision cutoff weight hw j top htop
      (g.eligible_of_le (hp top htop) hj he) x
  have hb (j : ℕ) (hj : j < N) : 0 < b j :=
    (hn (j+1) (by omega)).trans_le
      (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun i x => (hw i x).le) hK gap j (slope top) x).1
  have hpath := hierarchyWeight_eq_path_product n b (fun _ => (a : ℂ)) a N
    (hn N le_rfl) (fun j hj => hn (j+1) (by omega)) hb
  have hnorm := normalized_endpoint_telescope n b a N hn hb
  rw [hpath] at hnorm
  simpa only [packetPathProduct, Nat.Ico_zero_eq_range, sourceTransition, analyticTransition]
    using hnorm

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path mass at shifted block endpoints is set to zero as soon as
the distinguished top becomes ineligible, even if other tops continue.
The actual drop has the same factor-two reference-window comparison,
including this terminal block. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem shiftedPathMass_nonneg {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    0 ≤ g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  unfold shiftedPathMass
  split_ifs
  · exact Finset.sum_nonneg fun t _ => hw t x
  · exact le_rfl

theorem shiftedPathMass_antitone {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) :
    Antitone (g.shiftedPathMass tops slope precision cutoff weight σ top x) := by
  intro j k hjk
  have hlevel := (ShiftedBlocks.endpoint_strictMono hK σ).monotone hjk
  by_cases hk : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ k)
  · have hj := g.eligible_of_le (hp top htop) hlevel hk
    rw [shiftedPathMass,ite_eq_left hk,shiftedPathMass,ite_eq_left hj]
    exact g.path_mass_antitone tops slope precision cutoff weight hp hw top x hlevel
  · rw [shiftedPathMass,ite_eq_right hk]
    exact g.shiftedPathMass_nonneg tops slope precision cutoff weight hw σ top x j

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMassStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite mass stopping index. A terminal ineligible top has
zero path mass, so the source cutoff is attained without a positive lower
bound on any individual top weight. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem firstMassStop_spec (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) :
    firstMassStop n count M ≤ count ∧ n (firstMassStop n count M) ≤ M ∧
      ∀ j < firstMassStop n count M, M < n j := by
  have hex : ∃ j : ℕ, j ≤ count ∧ n j ≤ M := ⟨count,le_rfl,hlast⟩
  rw [firstMassStop,dite_eq_left hex]
  refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro j hj
  have hn := Nat.find_min hex hj
  have hcount := (Nat.le_of_lt hj).trans (Nat.find_spec hex).1
  exact lt_of_not_ge fun h => hn ⟨hcount,h⟩

theorem firstMassStop_after (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) {j : ℕ}
    (hj : firstMassStop n count M ≤ j) : n j ≤ M :=
  (hanti hj).trans (firstMassStop_spec n count M hlast).2.1

theorem firstMassStop_active_iff (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) (j : ℕ) :
    j < firstMassStop n count M ↔ M < n j := by
  constructor
  · exact (firstMassStop_spec n count M hlast).2.2 j
  · intro hj
    by_contra hn
    exact (not_lt_of_ge (firstMassStop_after n count M hlast hanti (Nat.le_of_not_gt hn))) hj

namespace AngularGrid

theorem shiftedPathMass_terminal_zero {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (σ : Fin K) (top : ι) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ count))
    (x : X) : g.shiftedPathMass tops slope precision cutoff weight σ top x count = 0 := by
  rw [shiftedPathMass,ite_eq_right hterminal]

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase and amplitude estimates at the actual source parameters. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem phaseMu_positive_le {D p : ℝ} (hD : 1 ≤ D) (hp : 0 < p) :
    0 < phaseMu D p ∧ phaseMu D p ≤ (4 / 3 : ℝ) / p := by
  have hθ := phaseParameter_range hD
  change 0 < phaseParameter D ∧ phaseParameter D ≤ 1 / 3 at hθ
  constructor
  · exact div_pos (by linarith [hθ.1]) hp
  · exact div_le_div_of_nonneg_right (by linarith [hθ.2]) hp.le

theorem source_phaseMu_small {D L : ℝ} (hD : 1 ≤ D) (hL : 256 ≤ L) :
    0 < phaseMu D (Real.sqrt L) ∧ phaseMu D (Real.sqrt L) ≤ 1 / 12 := by
  have hroot : (16 : ℝ) ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL
  have hp : 0 < Real.sqrt L := by linarith
  have hμ := phaseMu_positive_le hD hp
  refine ⟨hμ.1, hμ.2.trans ?_⟩
  exact (div_le_iff₀ hp).mpr (by linarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original length restrictions and the common top mask in the actual
source analytic amplitude. Small masks retain their full gain when the
single-top bounds are summed over an eligible angular node. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

variable {ι X : Type*}

theorem sourcePacketAmplitude_smul_value {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (top : σ → ι) (stop : σ → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (z : X) (level : ℕ) (cell : ℤ) (q : ℂ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets top stop
      (fun p => q • value p) phase a z level cell =
      q • g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets top stop
        value phase a z level cell := by
  unfold sourcePacketAmplitude packetAmplitude sourcePacketBase
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [smul_smul]
  congr 1
  ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularAmplitudeIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shared source amplitude is entire on every affine complex
line. Its equal-coordinate value gives exactly the boundary-weighted
packet sum, and its block identity uses the same amplitude for all shifts. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

/-- Exact source equation (30), summed over the packets of one root. -/
theorem sourcePacketAmplitude_equal_coordinates (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (x : X) (root : ℤ) :
    ((g.mass tops slope precision cutoff weight 0 root x ^ a : ℝ) : ℂ) •
      g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value (fun _ => (a : ℂ)) a x 0 root =
      ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop 0 root,
        ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
          (stop s) (assigned s) a x : ℝ) : ℂ) • value s := by
  unfold sourcePacketAmplitude packetAmplitude
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨hsp, hroot, _⟩ := Finset.mem_filter.mp hs
  have heq := g.source_normalized_endpoint tops slope precision cutoff weight hp hw hK gap
    (stop s) (assigned s) (hassigned s hsp) (heligible s hsp) a x
  dsimp only at heq
  rw [hroot] at heq
  simp only [sourcePacketBase, smul_smul]
  rw [← mul_assoc]
  simpa only [sourceBoundaryCoefficient, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun c : ℂ => c • value s) heq

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockChildren
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual block children are the nonempty eligible-top cells. Their
canonical representatives are slopes of eligible tops, including cells
whose packet amplitude is zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem sourceBlockTop_spec {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    let t := g.sourceBlockTop tops slope precision cutoff lower upper parent c
    t ∈ tops ∧ g.index lower (slope t) = parent ∧
      g.eligible cutoff (precision t) upper ∧ g.index upper (slope t) = c.val := by
  have h := (Finset.mem_image.mp c.property).choose_spec
  obtain ⟨hc,he⟩ := Finset.mem_filter.mp h.1
  have ht := (g.mem_cellTops tops slope precision cutoff lower parent _).mp hc
  exact ⟨ht.1,ht.2.1,he,h.2⟩

theorem sourceBlockTop_mem_child {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    g.sourceBlockTop tops slope precision cutoff lower upper parent c ∈
      g.cellTops tops slope precision cutoff upper c.val := by
  obtain ⟨ht,_,he,hi⟩ := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent c
  exact (g.mem_cellTops tops slope precision cutoff upper c.val _).mpr ⟨ht,hi,he⟩

theorem sourceBlockCells_nonempty_child {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    (g.cellTops tops slope precision cutoff upper c.val).Nonempty :=
  ⟨_,g.sourceBlockTop_mem_child tops slope precision cutoff lower upper parent c⟩

/-- Every eligible top in the parent selects one of these children. -/
theorem mem_sourceBlockCells_of_top {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hle : lower ≤ upper)
    (top : ι) (htop : top ∈ tops) (hparent : g.index lower (slope top) = parent)
    (he : g.eligible cutoff (precision top) upper) :
    g.index upper (slope top) ∈ g.sourceBlockCells tops slope precision cutoff lower upper parent := by
  apply Finset.mem_image.mpr
  refine ⟨top,Finset.mem_filter.mpr ⟨?_,he⟩,rfl⟩
  exact (g.mem_cellTops tops slope precision cutoff lower parent top).mpr
    ⟨htop,hparent,g.eligible_of_le (hp top htop) hle he⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNodeRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized prediction is exactly the source node ratio with its
packet residual removed. The denominator retains the stopped-top mass
and every nonempty eligible child, including zero-amplitude children. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem sourceNodeDenominator_stopped_mass (n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (α p : ℝ) :
    sourceNodeDenominator n c A α p = (n-∑ i, c i)+∑ i, vertexAmount (c i) (A i) α p := by
  simp only [sourceNodeDenominator,vertexAmount,Finset.sum_add_distrib]
  ring

theorem sourceNodeDenominator_pos {n : ℝ} (hn : 0 < n) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ) :
    0 < sourceNodeDenominator n c A α p := by
  apply add_pos_of_pos_of_nonneg hn
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hc i) _)
    (Real.rpow_nonneg (norm_nonneg _) _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite path-product argument in §10. Marked indices retain the
residual-free predictor; all consecutive unary runs use one common cubic
variation estimate. The remaining unmarked large-drop index is unique.
The estimates are independent of the number of angular levels. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

/-- The exceptional factor is controlled just by its amplitude and the
baseline mass in its denominator. -/
theorem source_exceptional_factor_le {E : Type*} [NormedAddCommGroup E]
    (A : E) {n denominator M C a p : ℝ}
    (hn : 0 < n) (hden : n ≤ denominator) (hM : n ≤ M+1)
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hp : 0 ≤ p) (hA : ‖A‖ ≤ C*n) :
    vertexAmount n A a p/denominator ≤ 1+C^p*(M+1)^(a-1) := by
  have henergy : n^(a-p)*‖A‖^p ≤ C^p*n^a := by
    calc
      _ ≤ n^(a-p)*(C*n)^p := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hA hp) (Real.rpow_nonneg hn.le _)
      _ = C^p*n^a := by
        rw [Real.mul_rpow hC hn.le]
        calc
          n^(a-p)*(C^p*n^p) = C^p*(n^(a-p)*n^p) := by ring
          _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring
  have hbase : vertexAmount n A a p/denominator ≤ vertexAmount n A a p/n :=
    div_le_div_of_nonneg_left (vertexAmount_pos (a := a) (p := p) hn A).le hn hden
  apply hbase.trans
  calc
    _ ≤ (n+C^p*n^a)/n := div_le_div_of_nonneg_right (by
      unfold vertexAmount
      linarith) hn.le
    _ = 1+C^p*n^(a-1) := by
      rw [add_div,div_self hn.ne',mul_div_assoc,← Real.rpow_sub_one hn.ne']
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hn.le hM (show 0 ≤ a-1 by linarith)) (Real.rpow_nonneg hC _))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FiniteGoodPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-path domination from an exact finite top expansion and the
proved individual terminal-probability cap. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {τ : Type*} [DecidableEq τ]

/-- The bad terminal tops carry at most half the original amount. -/
theorem finite_good_path_domination (S bad : Finset τ) (hbadS : bad ⊆ S)
    (w e Q : τ → ℝ) (V C : ℝ) (hV : 0 < V)
    (htotal : ∑ t ∈ S, e t*Q t = V)
    (hprob : ∀ t ∈ bad, e t*Q t/V ≤ C*w t)
    (he : ∀ t ∈ S, e t ≤ C*w t) (hQ : ∀ t ∈ S, 0 ≤ Q t)
    (hbad : C*(∑ t ∈ bad, w t) ≤ 1/2) :
    V ≤ 2*C*∑ t ∈ S\bad, w t*Q t := by
  classical
  have hbadAmount : (∑ t ∈ bad, e t*Q t) ≤ V/2 := by
    calc
      _ ≤ ∑ t ∈ bad, (C*w t)*V := Finset.sum_le_sum fun t ht =>
        (div_le_iff₀ hV).mp (hprob t ht)
      _ = (C*(∑ t ∈ bad, w t))*V := by rw [Finset.mul_sum,Finset.sum_mul]
      _ ≤ (1/2)*V := mul_le_mul_of_nonneg_right hbad hV.le
      _ = V/2 := by ring
  have hsplit := Finset.sum_sdiff hbadS (f := fun t => e t*Q t)
  rw [htotal] at hsplit
  have hgood : (∑ t ∈ S\bad, e t*Q t) ≤ C*∑ t ∈ S\bad, w t*Q t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have htS := (Finset.mem_sdiff.mp ht).1
    exact (mul_le_mul_of_nonneg_right (he t htS) (hQ t htS)).trans_eq (mul_assoc _ _ _)
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual finite source packet amplitudes. The
angular cells and packet stopping levels are fixed; only the spatial
weights and packet values vary. Vanishing masses are allowed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
namespace AngularGrid

variable {ι σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem measurable_mass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (level : ℕ) (cell : ℤ) :
    Measurable (g.mass tops slope precision cutoff weight level cell) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_boundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (base level : ℕ) (gap s : ℝ) :
    Measurable (g.boundaryMass tops slope precision cutoff weight base level gap s) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_sourceBoundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (level : ℕ) (cell : ℤ) :
    Measurable (g.sourceBoundaryMass tops slope precision cutoff weight K gap level cell) :=
  g.measurable_boundaryMass tops slope precision cutoff weight hw _ _ _ _

theorem measurable_sourceTransition (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x =>
      g.sourceTransition tops slope precision cutoff weight K gap phase x level cell) := by
  unfold sourceTransition analyticTransition
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw (level+1) cell).div
      (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap level cell)).log)).cexp

theorem measurable_packetPathProduct (g : AngularGrid) (transition : X → ℕ → ℤ → ℂ)
    (ht : ∀ level cell, Measurable (fun x => transition x level cell))
    (lower upper : ℕ) (slope : ℝ) :
    Measurable (fun x => g.packetPathProduct (transition x) lower upper slope) :=
  Finset.measurable_prod _ (fun j _ => ht j _)

theorem measurable_sourcePacketBase (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (a : ℝ) (s : σ) :
    Measurable (fun x => g.sourcePacketBase tops slope precision cutoff weight assigned stop
      (value x) a x s) := by
  unfold sourcePacketBase
  exact (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw _ _).pow_const (-a))).smul (hv s)

theorem measurable_sourcePacketAmplitude (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (phase : ℕ → ℂ)
    (a : ℝ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x level cell) := by
  unfold sourcePacketAmplitude packetAmplitude
  apply Finset.measurable_sum
  intro s _
  exact (g.measurable_packetPathProduct _
    (g.measurable_sourceTransition tops slope precision cutoff weight hw K gap phase) _ _ _).smul
    (g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s)

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNodeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the original source node ratios and the finite active
path product. These are the integrands used for line-to-plane gluing,
independently of any selected snapshot predictors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {X : Type*} {ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]

omit [MeasurableSpace X] in
theorem sourceActiveProduct_nonneg (n beta : X → ℕ → ℝ) (M : ℝ) (count : ℕ)
    (x : X) (hb : ∀ j < count, M < n x j → 0 ≤ beta x j) :
    0 ≤ sourceActiveProduct n beta M count x := by
  apply Finset.prod_nonneg
  intro j hj
  split_ifs with h
  · exact hb j (Finset.mem_range.mp hj) h
  · exact zero_le_one

omit [MeasurableSpace X] in
/-- The measurable active product agrees exactly with the finite prefix
ending at the first mass crossing. The terminal mass may be zero. -/
theorem sourceActiveProduct_eq_stopped_product (n beta : X → ℕ → ℝ)
    (M : ℝ) (count : ℕ) (x : X) (hfinal : n x count ≤ M) (hanti : Antitone (n x)) :
    sourceActiveProduct n beta M count x =
      ∏ j ∈ Finset.range (firstMassStop (n x) count M), beta x j := by
  let stop := firstMassStop (n x) count M
  have hs : stop ≤ count := (firstMassStop_spec (n x) count M hfinal).1
  unfold sourceActiveProduct
  calc
    _ = ∏ j ∈ Finset.range stop, if M < n x j then beta x j else 1 := by
      symm
      apply Finset.prod_subset (Finset.range_mono hs)
      intro j _ hj
      have hjs : ¬j < stop := fun h => hj (Finset.mem_range.mpr h)
      have hn : ¬M < n x j := fun h => hjs
        ((firstMassStop_active_iff (n x) count M hfinal hanti j).mpr h)
      simp only [ite_eq_right hn]
    _ = ∏ j ∈ Finset.range stop, beta x j := by
      apply Finset.prod_congr rfl
      intro j hj
      exact ite_eq_left ((firstMassStop_active_iff (n x) count M hfinal hanti j).mp
        (Finset.mem_range.mp hj))

theorem sourceNodeRatio_nonneg (n : ℝ) (hn : 0 ≤ n) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (parent : EuclideanSpace ℂ κ) : 0 ≤ sourceNodeRatio n c A α p parent := by
  unfold sourceNodeRatio sourceNodeDenominator vertexAmount
  exact div_nonneg
    (add_nonneg hn (mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (add_nonneg hn (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (Real.rpow_nonneg (hc i) _) (Real.rpow_nonneg (norm_nonneg _) _))))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite hierarchy path integrand, expressed only through
packet amplitudes, top weights and the stopping threshold. Its spatial
measurability does not involve the auxiliary snapshot choices. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

omit [MeasurableSpace X] in
theorem sourceBlockNodeRatio_nonneg (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (lower upper : ℕ) (parent : ℤ) (x : X) :
    0 ≤ g.sourceBlockNodeRatio tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p lower upper parent x := by
  unfold sourceBlockNodeRatio
  apply sourceNodeRatio_nonneg
  · exact g.mass_nonnegative tops slope precision cutoff weight hw lower parent x
  · intro i
    exact g.mass_nonnegative tops slope precision cutoff weight hw upper i.val x

omit [MeasurableSpace X] in
theorem sourceActivePathValue_nonneg {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ) (x : X) :
    0 ≤ g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p M tag top count x := by
  apply sourceActiveProduct_nonneg
  intro j _ _
  exact g.sourceBlockNodeRatio_nonneg tops slope precision cutoff weight hw K gap packets
    assigned stop value phase a α p _ _ _ x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The amplitude on a distinguished top path stops when that top becomes
ineligible. Other surviving children remain in the original denominator. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem sourceNodeDenominator_ge_mass {ι κ : Type} [Fintype ι] [Fintype κ]
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (hc : ∀ i, 0 ≤ c i) : n ≤ sourceNodeDenominator n c A α p := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hc i) _)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem sourceNodeDenominator_ge_child {ι κ : Type} [Fintype ι] [Fintype κ]
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (hc : ∀ i, 0 ≤ c i) (i : ι) :
    n-c i+vertexAmount (c i) (A i) α p ≤ sourceNodeDenominator n c A α p := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun k => (c k)^(α-p)*‖A k‖^p)
    (fun k _ => mul_nonneg (Real.rpow_nonneg (hc k) _)
      (Real.rpow_nonneg (norm_nonneg _) _)) (Finset.mem_univ i)
  dsimp only [vertexAmount,sourceNodeDenominator]
  linarith

namespace AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem source_active_path_eq_stopped_product {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ)
    (a α p M : ℝ) (hM : 0 ≤ M) (hKb : 0 < Kb) (tag : Fin Kb)
    (top : τ) (htop : top ∈ tops) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag count)) (x : X) :
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M tag top count x =
    ∏ j ∈ Finset.range
      (firstMassStop (g.shiftedPathMass tops slope precision cutoff weight tag top x) count M),
      g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
        phase a α p tag top x j := by
  apply sourceActiveProduct_eq_stopped_product
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight tag top count hterminal]
    exact hM
  · exact g.shiftedPathMass_antitone tops slope precision cutoff weight hprecision hweight
      hKb tag top htop x

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conservation on one source block, including the top weights
that stop before its upper endpoint. This is the row decomposition of
the original node denominator used by the finite path flow. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem sourceBlock_continuing_fiber (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent cell : ℤ)
    (hc : cell ∈ g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    ((g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => g.eligible cutoff (precision t) upper)).filter
        (fun t => g.index upper (slope t) = cell) =
      g.cellTops tops slope precision cutoff upper cell := by
  have hrep := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨cell,hc⟩
  ext t
  constructor
  · intro ht
    obtain ⟨hcont,hindex⟩ := Finset.mem_filter.mp ht
    obtain ⟨hparent,he⟩ := Finset.mem_filter.mp hcont
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨((g.mem_cellTops _ _ _ _ _ _ _).mp hparent).1,hindex,he⟩
  · intro ht
    have htop := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
    have hlo := g.eligible_of_le (hp t htop.1) hle htop.2.2
    have hindex : g.index lower (slope t) = parent := by
      have hi := g.index_eq_of_le hle (htop.2.1.trans hrep.2.2.2.symm)
      exact hi.trans hrep.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop.1,hindex,hlo⟩,htop.2.2⟩,htop.2.1⟩

theorem sum_sourceBlock_child_mass (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (lower upper : ℕ) (hle : lower ≤ upper)
    (parent : ℤ) (x : X) :
    (∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.mass tops slope precision cutoff weight upper c.val x) =
    ∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => g.eligible cutoff (precision t) upper), weight t x := by
  let continuing := (g.cellTops tops slope precision cutoff lower parent).filter
    (fun t => g.eligible cutoff (precision t) upper)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hf := Finset.sum_fiberwise_of_maps_to (s := continuing) (t := cells)
    (fun t ht => Finset.mem_image_of_mem (fun t => g.index upper (slope t)) ht)
    (fun t => weight t x)
  rw [← Finset.sum_coe_sort] at hf
  calc
    _ = ∑ c : cells, ∑ t ∈ continuing.filter (fun t => g.index upper (slope t) = c.val),
        weight t x := by
      apply Finset.sum_congr rfl
      intro c _
      rw [show continuing.filter (fun t => g.index upper (slope t) = c.val) =
        g.cellTops tops slope precision cutoff upper c.val from
        g.sourceBlock_continuing_fiber tops slope precision cutoff hp lower upper hle parent c.val c.property]
      rfl
    _ = _ := hf

/-- The stopping mass is an actual sum of original top weights. -/
theorem sourceBlock_mass_conservation (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (lower upper : ℕ) (hle : lower ≤ upper)
    (parent : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight lower parent x =
    (∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => ¬g.eligible cutoff (precision t) upper), weight t x)+
    ∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.mass tops slope precision cutoff weight upper c.val x := by
  rw [g.sum_sourceBlock_child_mass tops slope precision cutoff weight hp lower upper hle parent x]
  simpa only [not_not,mass] using (Finset.sum_filter_add_sum_filter_not
    (g.cellTops tops slope precision cutoff lower parent)
    (fun t => ¬g.eligible cutoff (precision t) upper) (fun t => weight t x)).symm

/-- Exact source denominator as continuing child amounts plus stopped
top weights; no mass is lost by grouping several angular levels. -/
theorem sourceBlock_denominator_conservation {κ : Type} [Fintype κ]
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (x : X)
    (A : g.sourceBlockCells tops slope precision cutoff lower upper parent → EuclideanSpace ℂ κ)
    (α p : ℝ) :
    sourceNodeDenominator (g.mass tops slope precision cutoff weight lower parent x)
      (fun c => g.mass tops slope precision cutoff weight upper c.val x) A α p =
    (∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => ¬g.eligible cutoff (precision t) upper), weight t x)+
    ∑ c, vertexAmount (g.mass tops slope precision cutoff weight upper c.val x) (A c) α p := by
  rw [sourceNodeDenominator_stopped_mass]
  have hm := g.sourceBlock_mass_conservation tops slope precision cutoff weight hp
    lower upper hle parent x
  rw [hm]
  ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite conservation for the actual angular partitions. Stopping
at a small-mass cell retains its normalized vertex amount; ineligible tops
retain their original weight. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

theorem sourceBlock_sum_continuing (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (F : τ → ℝ) :
    (∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      ∑ t ∈ g.cellTops tops slope precision cutoff upper c.val, F t) =
    ∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => g.eligible cutoff (precision t) upper), F t := by
  let continuing := (g.cellTops tops slope precision cutoff lower parent).filter
    (fun t => g.eligible cutoff (precision t) upper)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hf := Finset.sum_fiberwise_of_maps_to (s := continuing) (t := cells)
    (fun t ht => Finset.mem_image_of_mem (fun t => g.index upper (slope t)) ht) F
  rw [← Finset.sum_coe_sort] at hf
  calc
    _ = ∑ c : cells, ∑ t ∈ continuing.filter (fun t => g.index upper (slope t) = c.val), F t := by
      apply Finset.sum_congr rfl
      intro c _
      rw [g.sourceBlock_continuing_fiber tops slope precision cutoff hp lower upper hle
        parent c.val c.property]
    _ = _ := hf

theorem sourceBlock_weighted_sum (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (w F : τ → ℝ)
    (hstop : ∀ t ∈ g.cellTops tops slope precision cutoff lower parent,
      ¬g.eligible cutoff (precision t) upper → F t = 1) :
    (∑ t ∈ g.cellTops tops slope precision cutoff lower parent, w t*F t) =
    (∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => ¬g.eligible cutoff (precision t) upper), w t)+
    ∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      ∑ t ∈ g.cellTops tops slope precision cutoff upper c.val, w t*F t := by
  rw [g.sourceBlock_sum_continuing tops slope precision cutoff hp lower upper hle parent]
  rw [← Finset.sum_filter_add_sum_filter_not
    (g.cellTops tops slope precision cutoff lower parent)
    (fun t => ¬g.eligible cutoff (precision t) upper) (fun t => w t*F t)]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
    rw [hstop t ht he,mul_one]
  · simp only [not_not]

section Tree
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
  (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ → ℕ)
  (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p : ℝ) (x : X)

variable {g tops slope precision cutoff weight level A α p x}

theorem sourceTreeTail_ineligible (M : ℝ) (n j : ℕ) (t : τ)
    (he : ¬g.eligible cutoff (precision t) (level j)) :
    g.sourceTreeTail tops slope precision cutoff weight level A α p x M n j t = 1 := by
  cases n <;> simp [sourceTreeTail,sourceTreeExit,he]

theorem sourceTreeExit_sum (hw : ∀ t x, 0 < weight t x) (j : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level j) cell).Nonempty) :
    (∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
      weight t x*g.sourceTreeExit tops slope precision cutoff weight level A α p x j t) =
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell := by
  have hm : 0 < g.mass tops slope precision cutoff weight (level j) cell x := by
    obtain ⟨t,ht⟩ := hne
    exact g.mass_pos_of_member tops slope precision cutoff weight hw (level j) cell x ht
  calc
    _ = ∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell, weight t x*
        (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell/
          g.mass tops slope precision cutoff weight (level j) cell x) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
      simp only [sourceTreeExit,ite_eq_left ht'.2.2,ht'.2.1]
    _ = _ := by
      rw [← Finset.sum_mul]
      change g.mass tops slope precision cutoff weight (level j) cell x*(_/_) = _
      exact mul_div_cancel₀ _ hm.ne'

/-- A finite stopped expansion exactly recovers the original node amount.
No transition or path-probability identity is assumed. -/
theorem sourceTreeTail_sum (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hlevel : Monotone level) (M : ℝ)
    (n j : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level j) cell).Nonempty) :
    (∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
      weight t x*g.sourceTreeTail tops slope precision cutoff weight level A α p x M n j t) =
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell := by
  induction n generalizing j cell with
  | zero => exact sourceTreeExit_sum hw j cell hne
  | succ n ih =>
    have hm : 0 < g.mass tops slope precision cutoff weight (level j) cell x := by
      obtain ⟨t,ht⟩ := hne
      exact g.mass_pos_of_member tops slope precision cutoff weight hw (level j) cell x ht
    by_cases hactive : M < g.mass tops slope precision cutoff weight (level j) cell x
    · have hden : 0 < g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell := by
        unfold sourceTreeDenominator
        apply sourceNodeDenominator_pos hm
        intro c
        exact g.mass_nonnegative tops slope precision cutoff weight
          (fun t x => (hw t x).le) (level (j+1)) c.val x
      calc
        _ = (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell/
            g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell)*
            ∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
              weight t x*g.sourceTreeTail tops slope precision cutoff weight level A α p x M n (j+1) t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
          simp only [sourceTreeTail,ht'.2.1,ht'.2.2,true_and,ite_eq_left hactive]
          ring
        _ = (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell/
            g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell)*
            g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell := by
          congr 1
          rw [g.sourceBlock_weighted_sum tops slope precision cutoff hp (level j) (level (j+1))
            (hlevel (Nat.le_succ j)) cell (fun t => weight t x)
            (g.sourceTreeTail tops slope precision cutoff weight level A α p x M n (j+1))
            (fun t _ he => sourceTreeTail_ineligible M n (j+1) t he)]
          unfold sourceTreeDenominator
          rw [g.sourceBlock_denominator_conservation tops slope precision cutoff weight hp
            (level j) (level (j+1)) (hlevel (Nat.le_succ j)) cell x]
          congr 1
          apply Finset.sum_congr rfl
          intro c _
          exact ih (j+1) c.val (g.sourceBlockCells_nonempty_child tops slope precision cutoff
            (level j) (level (j+1)) cell c)
        _ = _ := div_mul_cancel₀ _ hden.ne'
    · calc
        _ = ∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
            weight t x*g.sourceTreeExit tops slope precision cutoff weight level A α p x j t := by
          apply Finset.sum_congr rfl
          intro t ht
          have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
          simp only [sourceTreeTail,ht'.2.1,hactive,and_false,ite_false, if_false]
        _ = _ := sourceTreeExit_sum hw j cell hne

end Tree
end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite angular-tree conservation law is exactly the stopped
product used in the analytic path estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

section Path
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
  (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ → ℕ)
  (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p : ℝ) (x : X)

variable {g tops slope precision cutoff weight level A α p x}

theorem sourceTreeTail_eq_scalar (M : ℝ) (n j : ℕ) (top : τ) :
    g.sourceTreeTail tops slope precision cutoff weight level A α p x M n j top =
    stoppedScalarExpansion
      (fun k => g.eligible cutoff (precision top) (level k) ∧
        M < g.mass tops slope precision cutoff weight (level k) (g.index (level k) (slope top)) x)
      (g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top)
      (fun k => g.sourceTreeExit tops slope precision cutoff weight level A α p x k top) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [sourceTreeTail,stoppedScalarExpansion,ih]
    rfl

theorem sourceTreeTail_eq_stopped (M : ℝ) (hM : 0 ≤ M) (count : ℕ) (top : τ)
    (hterminal : ¬g.eligible cutoff (precision top) (level count)) :
    let stop := firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x top) count M
    g.sourceTreeTail tops slope precision cutoff weight level A α p x M count 0 top =
      g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top*
        ∏ j ∈ Finset.range stop,
          g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top j := by
  dsimp only
  let n := g.sourceTreePathMass tops slope precision cutoff weight level x top
  have hlast : n count ≤ M := by
    simpa only [n,sourceTreePathMass,ite_eq_right hterminal] using hM
  have hs := firstMassStop_spec n count M hlast
  have hactive (j : ℕ) :
      (g.eligible cutoff (precision top) (level j) ∧
        M < g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x)
        ↔ M < n j := by
    by_cases he : g.eligible cutoff (precision top) (level j)
    · simp only [n,sourceTreePathMass,he,ite_true, if_true,true_and]
    · simp only [n,sourceTreePathMass,he,ite_false, if_false,false_and,not_lt_of_ge hM]
  rw [sourceTreeTail_eq_scalar]
  simpa only [Nat.zero_add] using stoppedScalarExpansion_eq
    (fun k => g.eligible cutoff (precision top) (level k) ∧
      M < g.mass tops slope precision cutoff weight (level k) (g.index (level k) (slope top)) x)
    (g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top)
    (fun k => g.sourceTreeExit tops slope precision cutoff weight level A α p x k top)
    count (firstMassStop n count M) 0 hs.1
    (fun j hj => (hactive (0+j)).mpr (by simpa using hs.2.2 j hj))
    (fun h => (not_lt_of_ge hs.2.1) (by
      simpa only [Nat.zero_add] using (hactive _).mp h))

/-- Exact terminal product expansion of the original node amount. -/
theorem sourceTree_terminal_expansion (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hlevel : Monotone level)
    (M : ℝ) (hM : 0 ≤ M) (count : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      ¬g.eligible cutoff (precision t) (level count)) :
    (∑ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      let stop := firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M
      weight t x*g.sourceTreeExit tops slope precision cutoff weight level A α p x stop t*
        ∏ j ∈ Finset.range stop,
          g.sourceTreePathRatio tops slope precision cutoff weight level A α p x t j) =
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0 cell := by
  have h := sourceTreeTail_sum (A := A) (α := α) (p := p) (x := x)
    hp hw hlevel M count 0 cell hne
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  rw [sourceTreeTail_eq_stopped M hM count t (hterminal t ht)]
  exact mul_assoc _ _ _

end Path
end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every child transition in the actual angular tree has mass at most
one. The terminal path weights therefore have the required uniform cap. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

section Path
variable {g : AngularGrid} {tops : Finset τ} {slope precision : τ → ℝ}
  {cutoff : ℝ} {weight : τ → X → ℝ} {level : ℕ → ℕ}
  {A : ℕ → ℤ → EuclideanSpace ℂ κ} {α p : ℝ} {x : X}

theorem sourceTreePathRatio_nonneg (hw : ∀ t x, 0 ≤ weight t x) (top : τ) (j : ℕ) :
    0 ≤ g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top j := by
  unfold sourceTreePathRatio sourceTreeAmount sourceTreeDenominator
  apply div_nonneg
  · exact (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x).trans
      (mass_le_vertexAmount (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x) _)
  · exact (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x).trans
      (sourceNodeDenominator_ge_mass _ _ _ α p
        (fun c => g.mass_nonnegative tops slope precision cutoff weight hw _ c.val x))

theorem sourceTreeExit_nonneg (hw : ∀ t x, 0 ≤ weight t x) (top : τ) (j : ℕ) :
    0 ≤ g.sourceTreeExit tops slope precision cutoff weight level A α p x j top := by
  unfold sourceTreeExit
  split_ifs
  · apply div_nonneg
    · exact (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x).trans
        (mass_le_vertexAmount (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x) _)
    · exact g.mass_nonnegative tops slope precision cutoff weight hw _ _ x
  · exact zero_le_one

theorem sourceTreeDenominator_ge_child_amount
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (hlevel : Monotone level) (top : τ) (htop : top ∈ tops) (j : ℕ)
    (he : g.eligible cutoff (precision top) (level (j+1))) :
    g.sourceTreeAmount tops slope precision cutoff weight level A α p x (j+1)
      (g.index (level (j+1)) (slope top)) ≤
    g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top)) := by
  let cells := g.sourceBlockCells tops slope precision cutoff (level j) (level (j+1))
    (g.index (level j) (slope top))
  have hc : g.index (level (j+1)) (slope top) ∈ cells :=
    g.mem_sourceBlockCells_of_top tops slope precision cutoff (level j) (level (j+1))
      (g.index (level j) (slope top)) hp (hlevel (Nat.le_succ j)) top htop rfl he
  have hm := g.path_mass_antitone tops slope precision cutoff weight hp hw top x
    (hlevel (Nat.le_succ j))
  have hd := sourceNodeDenominator_ge_child
    (g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x)
    (fun c : cells => g.mass tops slope precision cutoff weight (level (j+1)) c.val x)
    (fun c : cells => A (j+1) c.val) α p
    (fun c => g.mass_nonnegative tops slope precision cutoff weight hw _ c.val x)
    ⟨g.index (level (j+1)) (slope top),hc⟩
  change _ ≤ sourceNodeDenominator _ _ _ _ _
  unfold sourceTreeAmount
  linarith

/-- The product-to-root quotient has a uniform cap for every individual
terminal top; all preceding transitions use the actual child denominator. -/
theorem sourceTree_terminal_probability_le
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hlevel : Monotone level) (M : ℝ) (hM : 1 ≤ M)
    (count : ℕ) (top : τ) (htop : top ∈ tops)
    (hterminal : ¬g.eligible cutoff (precision top) (level count))
    (hroot : M < g.sourceTreePathMass tops slope precision cutoff weight level x top 0)
    (C : ℝ)
    (hexit : g.sourceTreeExit tops slope precision cutoff weight level A α p x
      (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x top) count M)
      top ≤ C) :
    weight top x*g.sourceTreeTail tops slope precision cutoff weight level A α p x M count 0 top/
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0
        (g.index (level 0) (slope top)) ≤ C*weight top x := by
  let n := g.sourceTreePathMass tops slope precision cutoff weight level x top
  let stop := firstMassStop n count M
  let V := fun j => g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
    (g.index (level j) (slope top))
  let D := fun j => g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
    (g.index (level j) (slope top))
  have hlast : n count ≤ M := by
    simp only [n,sourceTreePathMass,ite_eq_right hterminal]
    linarith
  have hs := firstMassStop_spec n count M hlast
  have hspos : 0 < stop := by
    by_contra hn
    have hz : stop = 0 := by omega
    have h := hs.2.1
    change n stop ≤ M at h
    rw [hz] at h
    exact (not_le_of_gt hroot) h
  have he (j : ℕ) (hj : j < stop) : g.eligible cutoff (precision top) (level j) := by
    have hn := hs.2.2 j hj
    by_contra h
    simp only [n,sourceTreePathMass,ite_eq_right h] at hn
    linarith
  have hnpos (j : ℕ) (hj : j < stop) :
      0 < g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x :=
    g.path_mass_pos tops slope precision cutoff weight hw _ top htop (he j hj) x
  have hV (j : ℕ) (hj : j ≤ stop-1) : 0 < V j :=
    vertexAmount_pos (hnpos j (by omega)) _
  have hDmass (j : ℕ) :
      g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x ≤ D j := by
    dsimp only [D,sourceTreeDenominator]
    apply sourceNodeDenominator_ge_mass
    intro c
    exact g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le)
      (level (j+1)) c.val x
  have hD (j : ℕ) (hj : j ≤ stop-1) : 0 < D j := (hnpos j (by omega)).trans_le (hDmass j)
  have hchild (j : ℕ) (hj : j < stop-1) : V (j+1) ≤ D j :=
    sourceTreeDenominator_ge_child_amount hp (fun t x => (hw t x).le) hlevel top htop j
      (he (j+1) (by omega))
  have hexit0 : 0 ≤ g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top :=
    sourceTreeExit_nonneg (fun t x => (hw t x).le) top stop
  have hfinal : 1 ≤ D (stop-1) := by
    have hn := hs.2.2 (stop-1) (by omega)
    rw [show n (stop-1) = g.mass tops slope precision cutoff weight (level (stop-1))
      (g.index (level (stop-1)) (slope top)) x by
        simp only [n,sourceTreePathMass,ite_eq_left (he (stop-1) (by omega))]] at hn
    exact hM.trans (hn.le.trans (hDmass (stop-1)))
  rw [sourceTreeTail_eq_stopped M (by linarith) count top hterminal]
  have hstop : stop-1+1 = stop := by omega
  have hbound := normalized_terminal_weight_bound V D (stop-1)
    (weight top x*g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top)
    C (weight top x) hV hD hchild (mul_nonneg (hw top x).le hexit0)
    ((mul_le_mul_of_nonneg_left hexit (hw top x).le).trans_eq (mul_comm _ _)) hfinal
  rw [hstop] at hbound
  simpa only [V,D,sourceTreePathRatio,mul_assoc] using hbound

end Path
end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeGoodPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The good-path domination inequality for the original finite angular
tree, derived from its exact expansion and actual child transitions. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable Classical.decEq
variable {τ X : Type*} {κ : Type} [Fintype κ]

theorem sourceTree_good_path_domination
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (level : ℕ → ℕ) (hlevel : Monotone level)
    (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p M C : ℝ) (hM : 1 ≤ M)
    (x : X) (count : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level 0) cell).Nonempty)
    (hroot : M < g.mass tops slope precision cutoff weight (level 0) cell x)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      ¬g.eligible cutoff (precision t) (level count))
    (hexit : ∀ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      g.sourceTreeExit tops slope precision cutoff weight level A α p x
        (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M) t ≤ C)
    (bad : Finset τ) (hbadS : bad ⊆ g.cellTops tops slope precision cutoff (level 0) cell)
    (hbad : C*(∑ t ∈ bad, weight t x) ≤ 1/2) :
    g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0 cell ≤
      2*C*∑ t ∈ g.cellTops tops slope precision cutoff (level 0) cell\bad,
        weight t x*∏ j ∈ Finset.range
          (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M),
          g.sourceTreePathRatio tops slope precision cutoff weight level A α p x t j := by
  let S := g.cellTops tops slope precision cutoff (level 0) cell
  let finish := fun t => firstMassStop
    (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M
  let Q := fun t => ∏ j ∈ Finset.range (finish t),
    g.sourceTreePathRatio tops slope precision cutoff weight level A α p x t j
  let e := fun t => weight t x*
    g.sourceTreeExit tops slope precision cutoff weight level A α p x (finish t) t
  let V := g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0 cell
  have hV : 0 < V := vertexAmount_pos (lt_trans (by linarith : 0 < M) hroot) _
  have htotal : ∑ t ∈ S, e t*Q t = V :=
    g.sourceTree_terminal_expansion hp hw hlevel M (by linarith) count cell hne hterminal
  have hprob : ∀ t ∈ bad, e t*Q t/V ≤ C*weight t x := by
    intro t ht
    have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp (hbadS ht)
    have hr : M < g.sourceTreePathMass tops slope precision cutoff weight level x t 0 := by
      simpa only [sourceTreePathMass,ite_eq_left ht'.2.2,ht'.2.1] using hroot
    have hb := sourceTree_terminal_probability_le (A := A) (α := α) (p := p) hp hw hlevel
      M hM count t ht'.1 (hterminal t (hbadS ht)) hr C (hexit t (hbadS ht))
    rw [sourceTreeTail_eq_stopped M (by linarith) count t (hterminal t (hbadS ht))] at hb
    simpa only [ht'.2.1,e,Q,V,finish,mul_assoc] using hb
  have he : ∀ t ∈ S, e t ≤ C*weight t x := by
    intro t ht
    exact (mul_le_mul_of_nonneg_left (hexit t ht) (hw t x).le).trans_eq (mul_comm _ _)
  have hQ : ∀ t ∈ S, 0 ≤ Q t := by
    intro t _
    exact Finset.prod_nonneg fun j _ => sourceTreePathRatio_nonneg (fun t x => (hw t x).le) t j
  exact finite_good_path_domination S bad hbadS (fun t => weight t x) e Q V C
    hV htotal hprob he hQ hbad

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeExitBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary amplitude envelope gives the actual mass-stop cost.
No positive lower bound on a stopped top weight is needed. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

 theorem sourceTree_stop_exit_bound
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (level : ℕ → ℕ) (A : ℕ → ℤ → EuclideanSpace ℂ κ)
    (α p M C : ℝ) (hα : 1 ≤ α) (hp : 0 ≤ p) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (x : X) (count : ℕ) (top : τ) (htop : top ∈ tops)
    (hterminal : ¬g.eligible cutoff (precision top) (level count))
    (hamp : ∀ j ≤ count, g.eligible cutoff (precision top) (level j) →
      ‖A j (g.index (level j) (slope top))‖ ≤
        C*g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x) :
    g.sourceTreeExit tops slope precision cutoff weight level A α p x
      (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x top) count M) top ≤
      1+C^p*(M+1)^(α-1) := by
  let n := g.sourceTreePathMass tops slope precision cutoff weight level x top
  let stop := firstMassStop n count M
  have hlast : n count ≤ M := by
    simpa only [n,sourceTreePathMass,ite_eq_right hterminal] using hM
  have hs := firstMassStop_spec n count M hlast
  change g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top ≤ _
  unfold sourceTreeExit
  split_ifs with he
  · have hn := g.path_mass_pos tops slope precision cutoff weight hw (level stop) top htop he x
    have hsmall : g.mass tops slope precision cutoff weight (level stop)
        (g.index (level stop) (slope top)) x ≤ M+1 := by
      have hm := hs.2.1
      change n stop ≤ M at hm
      rw [show n stop = g.mass tops slope precision cutoff weight (level stop)
        (g.index (level stop) (slope top)) x by
          simp only [n,sourceTreePathMass,ite_eq_left he]] at hm
      linarith
    exact source_exceptional_factor_le _ hn le_rfl hsmall hC hα hp (hamp stop hs.1 he)
  · exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hC _)
      (Real.rpow_nonneg (by linarith) _))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceTreePacketPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite tree conservation law uses precisely the original packet
active path. The node envelope controls its terminal cost, so deleting
the small bad-top mass yields domination by the good physical paths. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
  (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ)
  (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
  (phase : ℕ → ℂ) (a α p : ℝ) {Kb : ℕ} (shift : Fin Kb) (x : X)

theorem sourceTree_packet_active_path (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hKb : 0 < Kb) (top : τ) (htop : top ∈ tops)
    (count : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift count)) :
    (∏ j ∈ Finset.range (firstMassStop
      (g.sourceTreePathMass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift) x top)
      count M),
      g.sourceTreePathRatio tops slope precision cutoff weight (ShiftedBlocks.endpoint shift)
        (fun j cell => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
          packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift j) cell)
        α p x top j) =
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M shift top count x := by
  rw [g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp hw
    K gap packets assigned stop value phase a α p M hM hKb shift top htop count hterminal x]
  rfl

theorem sourceTree_packet_good_path_domination
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x) (hKb : 0 < Kb)
    (count : ℕ) (cell : ℤ) (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hα : 1 ≤ α) (hp0 : 0 ≤ p)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hroot : M < g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (bad : Finset τ)
    (hbadS : bad ⊆ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell)
    (hbad : (1+C^p*(M+1)^(α-1))*(∑ t ∈ bad, weight t x) ≤ 1/2) :
    vertexAmount (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell) α p ≤
      2*(1+C^p*(M+1)^(α-1))*
        ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell\bad,
          weight t x*g.sourceActivePathValue tops slope precision cutoff weight K gap packets
            assigned stop value phase a α p M shift t count x := by
  let A := fun j cell => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
    packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift j) cell
  have hexit (t : τ)
      (ht : t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell) :
      g.sourceTreeExit tops slope precision cutoff weight (ShiftedBlocks.endpoint shift) A α p x
        (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight
          (ShiftedBlocks.endpoint shift) x t) count M) t ≤ 1+C^p*(M+1)^(α-1) := by
    have htt := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
    exact g.sourceTree_stop_exit_bound tops slope precision cutoff weight hw
      (ShiftedBlocks.endpoint shift) A α p M C hα hp0 (zero_le_one.trans hM) hC x count
      t htt.1 (hterminal t ht) (fun j hj _ => henvelope j hj _)
  have h := g.sourceTree_good_path_domination tops slope precision cutoff weight hp hw
    (ShiftedBlocks.endpoint shift) (ShiftedBlocks.endpoint_strictMono hKb shift).monotone
    A α p M (1+C^p*(M+1)^(α-1)) hM x count cell hne hroot hterminal hexit bad hbadS hbad
  change vertexAmount _ _ _ _ ≤ _ at h
  apply h.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have htt := (g.mem_cellTops _ _ _ _ _ _ _).mp (Finset.mem_sdiff.mp ht).1
  rw [g.sourceTree_packet_active_path tops slope precision cutoff weight K gap packets assigned
    stop value phase a α p shift x hp (fun t x => (hw t x).le) hKb t htt.1 count M
    (zero_le_one.trans hM) (hterminal t (Finset.mem_sdiff.mp ht).1)]

/-- A single pointwise majorant treats both small and active root masses.
Its two terms are the ordinary top mass and the already integrated good
physical paths, with the same terminal-envelope constant. -/
theorem sourceTree_packet_vertex_bound
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x) (hKb : 0 < Kb)
    (count : ℕ) (cell : ℤ) (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hα : 1 ≤ α) (hp0 : 0 ≤ p)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (bad : Finset τ)
    (hbadS : bad ⊆ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell)
    (hbad : (1+C^p*(M+1)^(α-1))*(∑ t ∈ bad, weight t x) ≤ 1/2) :
    vertexAmount (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell) α p ≤
      (1+C^p*(M+1)^(α-1))*
        g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x+
      2*(1+C^p*(M+1)^(α-1))*
        ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell\bad,
          weight t x*g.sourceActivePathValue tops slope precision cutoff weight K gap packets
            assigned stop value phase a α p M shift t count x := by
  have hmass : 0 < g.mass tops slope precision cutoff weight
      (ShiftedBlocks.endpoint shift 0) cell x := by
    obtain ⟨t,ht⟩ := hne
    exact g.mass_pos_of_member tops slope precision cutoff weight hw _ _ x ht
  have hcost : 0 ≤ 1+C^p*(M+1)^(α-1) := by positivity
  have hsum : 0 ≤ ∑ t ∈
      g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell\bad,
      weight t x*g.sourceActivePathValue tops slope precision cutoff weight K gap packets
        assigned stop value phase a α p M shift t count x := by
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (hw t x).le
      (g.sourceActivePathValue_nonneg tops slope precision cutoff weight
        (fun t x => (hw t x).le) K gap packets assigned stop value phase a α p M shift t count x)
  by_cases hroot : M < g.mass tops slope precision cutoff weight
      (ShiftedBlocks.endpoint shift 0) cell x
  · have h := g.sourceTree_packet_good_path_domination tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p shift x hp hw hKb count cell M C hM hC hα hp0
      hne hroot hterminal henvelope bad hbadS hbad
    exact h.trans (le_add_of_nonneg_left (mul_nonneg hcost hmass.le))
  · have hb := source_exceptional_factor_le
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell)
      hmass le_rfl (show g.mass tops slope precision cutoff weight
        (ShiftedBlocks.endpoint shift 0) cell x ≤ M+1 by linarith [le_of_not_gt hroot])
      hC hα hp0 (henvelope 0 (Nat.zero_le _) cell)
    have hsmall := (div_le_iff₀ hmass).mp hb
    exact hsmall.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hsum))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_GaussianPhaseDamping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian damping of the finite shift parameters. Its exact norm
removes the crude exp(C√L) growth outside the imaginary ball of radius L². -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem gaussianPhaseDamping_norm (a eta : ι → ℝ) :
    ‖gaussianPhaseDamping (phaseTubePoint a eta)‖ =
      Real.exp ((∑ i, (a i)^2)-(∑ i, (eta i)^2)) := by
  rw [gaussianPhaseDamping,Complex.norm_exp]
  congr 1
  rw [← Finset.sum_sub_distrib]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [phaseTubePoint,pow_two,Complex.mul_re]

theorem gaussianPhaseDamping_affine_entire (a b eta : ι → ℝ) :
    Differentiable ℂ (fun z => gaussianPhaseDamping (phaseTubeLine a b eta z)) := by
  unfold gaussianPhaseDamping
  apply Differentiable.cexp
  apply Differentiable.fun_sum
  intro i _
  dsimp only [phaseTubeLine]
  fun_prop

theorem gaussianPhaseDamping_simplex_le (a eta : ι → ℝ) (mu : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = mu) :
    ‖gaussianPhaseDamping (phaseTubePoint a eta)‖ ≤
      Real.exp (mu^2-∑ i, (eta i)^2) := by
  rw [gaussianPhaseDamping_norm]
  apply Real.exp_le_exp.mpr
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := a) (fun i _ => ha i)
  rw [hsum] at h
  linarith

theorem eventually_gaussian_imaginary_tail (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ mu r : ℝ, 0 ≤ mu → mu ≤ 1 → L^2 ≤ r →
      (1+r)*Real.exp (mu^2-r^2+C*Real.sqrt L) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (max 2 (C^2))] with L hL
  intro mu r hmu hmu1 hr
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L := by linarith
  have hCsq : C^2 ≤ L := (le_max_right _ _).trans hL
  have hCp : C ≤ Real.sqrt L := (Real.le_sqrt hC hL0).mpr hCsq
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hCL : C*Real.sqrt L ≤ L := by nlinarith [Real.sq_sqrt hL0]
  have hr4 : 4 ≤ r := by nlinarith
  have hLr : L ≤ r := by nlinarith
  have hmu2 : mu^2 ≤ 1 := by nlinarith
  have he : r+(mu^2-r^2+C*Real.sqrt L) ≤ 0 := by nlinarith
  calc
    _ ≤ Real.exp r*Real.exp (mu^2-r^2+C*Real.sqrt L) :=
      mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp r)
        (Real.exp_pos _).le
    _ = Real.exp (r+(mu^2-r^2+C*Real.sqrt L)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr he
    _ = 1 := Real.exp_zero

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DampedSimplexInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The damped scalar simplex estimate gives the undamped estimate at
its real barycenter. These are precisely the interpolation and damping
operations used for the source family in manuscript §11. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem gaussianPhaseDamping_real_ge_one (a : ι → ℝ) :
    1 ≤ ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))‖ := by
  rw [gaussianPhaseDamping_norm]
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero,sub_zero]
  exact Real.one_le_exp_iff.mpr (Finset.sum_nonneg fun i _ => sq_nonneg (a i))

theorem gaussian_undamp_real (F : (ι → ℂ) → ℂ) (a : ι → ℝ) (C : ℝ)
    (h : ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))*
      F (phaseTubePoint a (fun _ => 0))‖ ≤ C) :
    ‖F (phaseTubePoint a (fun _ => 0))‖ ≤ C := by
  calc
    _ ≤ ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))‖*
        ‖F (phaseTubePoint a (fun _ => 0))‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (gaussianPhaseDamping_real_ge_one a)
    _ = ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))*
        F (phaseTubePoint a (fun _ => 0))‖ := (norm_mul _ _).symm
    _ ≤ C := h

theorem damped_simplex_barycenter [DecidableEq ι] [Nonempty ι]
    (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ)) (hD : Convex ℝ D)
    (C mu : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) M a)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) C (Pi.single i mu)) :
    ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))‖ ≤ C := by
  have h := phaseTubeBound_barycenter (fun z => gaussianPhaseDamping z*F z) D hD C mu hC
    (fun a ha b hb eta => (gaussianPhaseDamping_affine_entire a b eta).mul
      (hentire a ha b hb eta)) hbounded hvertices hvertex
  exact gaussian_undamp_real F _ C (h (fun _ => 0))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceExponentialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration of the scalar exponential terms appearing in a source
packet amplitude. On each exhaustion set the logarithmic coefficients
are bounded, so the integrated affine slice is entire. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem source_affine_exp_norm_le {c d z : ℂ} {B R : ℝ}
    (_hB : 0 ≤ B) (hR : 0 ≤ R) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (c+z*d)‖ ≤ Real.exp (B+R*B) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖c+z*d‖ := Complex.re_le_norm _
    _ ≤ ‖c‖+‖z*d‖ := norm_add_le _ _
    _ = ‖c‖+‖z‖*‖d‖ := by rw [norm_mul]
    _ ≤ B+R*B := add_le_add hc (mul_le_mul hz hd (norm_nonneg _) hR)

theorem source_integral_affine_exp_entire (μ : Measure X)
    (a c d : X → ℂ) (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (haint : Integrable a μ) (B : ℝ) (hB : 0 ≤ B)
    (hcB : ∀ x, ‖c x‖ ≤ B) (hdB : ∀ x, ‖d x‖ ≤ B) :
    Differentiable ℂ (fun z => ∫ x, a x*Complex.exp (c x+z*d x) ∂μ) := by
  intro z0
  have hmeas (z : ℂ) : Measurable (fun x => a x*Complex.exp (c x+z*d x)) :=
    ha.mul (Complex.continuous_exp.measurable.comp (hc.add (hd.const_mul z)))
  have hpoint (z : ℂ) (x : X) :
      ‖a x*Complex.exp (c x+z*d x)‖ ≤ ‖a x‖*Real.exp (B+‖z‖*B) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (source_affine_exp_norm_le hB (norm_nonneg z) (hcB x) (hdB x) le_rfl) (norm_nonneg _)
  have hint (z : ℂ) : Integrable (fun x => a x*Complex.exp (c x+z*d x)) μ :=
    (haint.norm.mul_const (Real.exp (B+‖z‖*B))).mono' (hmeas z).aestronglyMeasurable
      (Eventually.of_forall (hpoint z))
  let derivative := fun z x => a x*(Complex.exp (c x+z*d x)*d x)
  have hderiv (z : ℂ) (x : X) : HasDerivAt
      (fun z => a x*Complex.exp (c x+z*d x)) (derivative z x) z := by
    simpa only [one_mul,derivative,id_eq] using
      ((((hasDerivAt_id z).mul_const (d x)).const_add (c x)).cexp).const_mul (a x)
  have hDmeas : AEStronglyMeasurable (derivative z0) μ :=
    (ha.mul ((Complex.continuous_exp.measurable.comp (hc.add (hd.const_mul z0))).mul hd)).aestronglyMeasurable
  have hDbound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball z0 1,
      ‖derivative z x‖ ≤ ‖a x‖*(Real.exp (B+(‖z0‖+1)*B)*B) := by
    apply Eventually.of_forall
    intro x z hz
    have hzR : ‖z‖ ≤ ‖z0‖+1 := (norm_lt_of_mem_ball hz).le
    have he := source_affine_exp_norm_le hB (by positivity : 0 ≤ ‖z0‖+1)
      (hcB x) (hdB x) hzR
    dsimp only [derivative]
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul he (hdB x) (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z0 (by norm_num : (0:ℝ) < 1))
    (Eventually.of_forall fun z => (hmeas z).aestronglyMeasurable) (hint z0) hDmeas hDbound
    (haint.norm.mul_const (Real.exp (B+(‖z0‖+1)*B)*B))
    (Eventually.of_forall fun x z _ => hderiv z x)
  exact h.2.differentiableAt

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source packet path is a single exponential of the sum of
its logarithmic transition ratios. This exact formula is used to integrate
an affine phase slice on sets where those finitely many logs are bounded. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem packetPathProduct_affine_exp (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (offset direction : ℕ → ℂ) (lower upper : ℕ) (slope : ℝ) (z : ℂ) :
    g.packetPathProduct (analyticTransition mass boundary (fun j => offset j+z*direction j))
      lower upper slope =
    Complex.exp (g.pathLogCombination mass boundary offset lower upper slope+
      z*g.pathLogCombination mass boundary direction lower upper slope) := by
  unfold packetPathProduct analyticTransition pathLogCombination
  rw [← Complex.exp_sum]
  congr 1
  simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourcePacketAmplitude_affine_exp (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (offset direction : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) (z : ℂ) :
    let mass := fun j c => g.mass tops slope precision cutoff weight j c x
    let boundary := fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop value
      (fun j => offset j+z*direction j) a x level cell =
    ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
      Complex.exp (g.pathLogCombination mass boundary offset level (stop s) (slope (assigned s))+
        z*g.pathLogCombination mass boundary direction level (stop s) (slope (assigned s))) •
        g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x s := by
  intro mass boundary
  unfold sourcePacketAmplitude packetAmplitude
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact g.packetPathProduct_affine_exp mass boundary offset direction level (stop s) (slope (assigned s)) z

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceFiniteExponentialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums of the exact packet-path exponentials may be integrated
against bounded Hilbert-valued tests on a bounded exhaustion. -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert
variable {X σ κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem source_affine_exp_integrable (μ : Measure X)
    (a c d : X → ℂ) (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (haint : Integrable a μ) (B : ℝ) (hB : 0 ≤ B)
    (hcB : ∀ x, ‖c x‖ ≤ B) (hdB : ∀ x, ‖d x‖ ≤ B) (z : ℂ) :
    Integrable (fun x => a x*Complex.exp (c x+z*d x)) μ := by
  apply (haint.norm.mul_const (Real.exp (B+‖z‖*B))).mono'
    (ha.mul (Complex.continuous_exp.measurable.comp (hc.add (hd.const_mul z)))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖a x*Complex.exp (c x+z*d x)‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (source_affine_exp_norm_le hB (norm_nonneg z) (hcB x) (hdB x) le_rfl) (norm_nonneg _)

theorem source_integral_finset_affine_exp_entire (μ : Measure X) (S : Finset σ)
    (a c d : σ → X → ℂ) (ha : ∀ s ∈ S, Measurable (a s))
    (hc : ∀ s ∈ S, Measurable (c s)) (hd : ∀ s ∈ S, Measurable (d s))
    (haint : ∀ s ∈ S, Integrable (a s) μ) (B : σ → ℝ) (hB : ∀ s ∈ S, 0 ≤ B s)
    (hcB : ∀ s ∈ S, ∀ x, ‖c s x‖ ≤ B s) (hdB : ∀ s ∈ S, ∀ x, ‖d s x‖ ≤ B s) :
    Differentiable ℂ (fun z => ∫ x, ∑ s ∈ S, a s x*Complex.exp (c s x+z*d s x) ∂μ) := by
  have heq : (fun z => ∫ x, ∑ s ∈ S, a s x*Complex.exp (c s x+z*d s x) ∂μ) =
      fun z => ∑ s ∈ S, ∫ x, a s x*Complex.exp (c s x+z*d s x) ∂μ := by
    funext z
    exact integral_finsetSum S (fun s hs => source_affine_exp_integrable μ _ _ _
      (ha s hs) (hc s hs) (hd s hs) (haint s hs) (B s) (hB s hs) (hcB s hs) (hdB s hs) z)
  rw [heq]
  apply Differentiable.fun_sum
  intro s hs
  exact source_integral_affine_exp_entire μ _ _ _ (ha s hs) (hc s hs) (hd s hs)
    (haint s hs) (B s) (hB s hs) (hcB s hs) (hdB s hs)

theorem source_integral_finite_exponential_pairing_entire
    (μ : Measure X) [IsFiniteMeasure μ] (S : Finset σ)
    (v : σ → X → EuclideanSpace ℂ κ) (c d : σ → X → ℂ)
    (hv : ∀ s ∈ S, Measurable (v s)) (hc : ∀ s ∈ S, Measurable (c s))
    (hd : ∀ s ∈ S, Measurable (d s)) (V B : σ → ℝ) (hB : ∀ s ∈ S, 0 ≤ B s)
    (hvV : ∀ s ∈ S, ∀ x, ‖v s x‖ ≤ V s)
    (hcB : ∀ s ∈ S, ∀ x, ‖c s x‖ ≤ B s) (hdB : ∀ s ∈ S, ∀ x, ‖d s x‖ ≤ B s)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b)
    (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x,
      ⟪b x,∑ s ∈ S, Complex.exp (c s x+z*d s x) • v s x⟫_ℂ ∂μ) := by
  have hpint (s : σ) (hs : s ∈ S) : Integrable (fun x => ⟪b x,v s x⟫_ℂ) μ := by
    apply (integrable_const (|T| * |V s|)).mono' (hb.inner (hv s hs)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul ((hbT x).trans (le_abs_self _)) ((hvV s hs x).trans (le_abs_self _))
        (norm_nonneg _) (abs_nonneg _))
  simp_rw [inner_sum,inner_smul_right,mul_comm (Complex.exp _) _]
  exact source_integral_finset_affine_exp_entire μ S (fun s x => ⟪b x,v s x⟫_ℂ) c d
    (fun s hs => hb.inner (hv s hs)) hc hd hpint B hB hcB hdB

theorem source_integral_finite_exponential_pairing_entire_on
    (μ : Measure X) [IsFiniteMeasure μ] (S : Finset σ) (A : Set X) (hA : MeasurableSet A)
    (v : σ → X → EuclideanSpace ℂ κ) (c d : σ → X → ℂ)
    (hv : ∀ s ∈ S, Measurable (v s)) (hc : ∀ s ∈ S, Measurable (c s))
    (hd : ∀ s ∈ S, Measurable (d s)) (V B : σ → ℝ)
    (hV : ∀ s ∈ S, 0 ≤ V s) (hB : ∀ s ∈ S, 0 ≤ B s)
    (hvV : ∀ s ∈ S, ∀ x ∈ A, ‖v s x‖ ≤ V s)
    (hcB : ∀ s ∈ S, ∀ x ∈ A, ‖c s x‖ ≤ B s)
    (hdB : ∀ s ∈ S, ∀ x ∈ A, ‖d s x‖ ≤ B s)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b)
    (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x in A,
      ⟪b x,∑ s ∈ S, Complex.exp (c s x+z*d s x) • v s x⟫_ℂ ∂μ) := by
  classical
  let v' := fun s => A.indicator (v s)
  let c' := fun s => A.indicator (c s)
  let d' := fun s => A.indicator (d s)
  have hv' : ∀ s ∈ S, Measurable (v' s) := fun s hs => (hv s hs).indicator hA
  have hc' : ∀ s ∈ S, Measurable (c' s) := fun s hs => (hc s hs).indicator hA
  have hd' : ∀ s ∈ S, Measurable (d' s) := fun s hs => (hd s hs).indicator hA
  have hvV' : ∀ s ∈ S, ∀ x, ‖v' s x‖ ≤ V s := by
    intro s hs x
    by_cases hx : x ∈ A
    · simpa only [v',Set.indicator_of_mem hx] using hvV s hs x hx
    · simpa only [v',Set.indicator_of_notMem hx,norm_zero] using hV s hs
  have hcB' : ∀ s ∈ S, ∀ x, ‖c' s x‖ ≤ B s := by
    intro s hs x
    by_cases hx : x ∈ A
    · simpa only [c',Set.indicator_of_mem hx] using hcB s hs x hx
    · simpa only [c',Set.indicator_of_notMem hx,norm_zero] using hB s hs
  have hdB' : ∀ s ∈ S, ∀ x, ‖d' s x‖ ≤ B s := by
    intro s hs x
    by_cases hx : x ∈ A
    · simpa only [d',Set.indicator_of_mem hx] using hdB s hs x hx
    · simpa only [d',Set.indicator_of_notMem hx,norm_zero] using hB s hs
  have heq : (fun z => ∫ x in A, ⟪b x,∑ s ∈ S,
      Complex.exp (c s x+z*d s x) • v s x⟫_ℂ ∂μ) =
      (fun z => ∫ x in A, ⟪b x,∑ s ∈ S,
      Complex.exp (c' s x+z*d' s x) • v' s x⟫_ℂ ∂μ) := by
    funext z
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hA] with x hx
    simp only [v',c',d',Set.indicator_of_mem hx]
  rw [heq]
  exact source_integral_finite_exponential_pairing_entire (μ.restrict A) S v' c' d'
    hv' hc' hd' V B hB hvV' hcB' hdB' b hb T hbT

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrated affine slices of the original source packet amplitude
are entire on bounded logarithmic-coefficient exhaustions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem measurable_sourcePathLog (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (s : ℝ) :
    Measurable (g.sourcePathLog tops slope precision cutoff weight K gap phase lower upper s) := by
  unfold sourcePathLog pathLogCombination
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (((g.measurable_mass tops slope precision cutoff weight hw _ _).div
    (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap _ _)).log.complex_ofReal)

theorem sourcePacketAmplitude_integral_affine_entire_on
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (offset direction : ℕ → ℂ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (A : Set X) (hA : MeasurableSet A) (V B : σ → ℝ)
    (hV : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, 0 ≤ V s)
    (hB : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, 0 ≤ B s)
    (hvV : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, ∀ x ∈ A,
      ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ ≤ V s)
    (hcB : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, ∀ x ∈ A,
      ‖g.sourcePathLog tops slope precision cutoff weight K gap offset level (stop s)
        (slope (assigned s)) x‖ ≤ B s)
    (hdB : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, ∀ x ∈ A,
      ‖g.sourcePathLog tops slope precision cutoff weight K gap direction level (stop s)
        (slope (assigned s)) x‖ ≤ B s)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b) (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x in A, ⟪b x,
      g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (fun j => offset j+z*direction j) a x level cell⟫_ℂ ∂μ) := by
  have heq (z : ℂ) (x : X) := g.sourcePacketAmplitude_affine_exp tops slope precision cutoff
    weight K gap packets assigned stop (value x) offset direction a x level cell z
  simp only at heq
  simp_rw [heq]
  exact source_integral_finite_exponential_pairing_entire_on μ
    (g.packetSet packets (fun s => slope (assigned s)) stop level cell) A hA
    (fun s x => g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s)
    (fun s => g.sourcePathLog tops slope precision cutoff weight K gap offset level (stop s) (slope (assigned s)))
    (fun s => g.sourcePathLog tops slope precision cutoff weight K gap direction level (stop s) (slope (assigned s)))
    (fun s _ => g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s)
    (fun s _ => g.measurable_sourcePathLog tops slope precision cutoff weight hw K gap offset level (stop s) _)
    (fun s _ => g.measurable_sourcePathLog tops slope precision cutoff weight hw K gap direction level (stop s) _)
    V B hV hB hvV hcB hdB b hb T hbT

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeVertexIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the actual finite packet-tree vertex bound. The only
path inputs are the restricted good-path integrals, which are supplied
by the marked line and plane estimates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ] [MeasurableSpace X]

theorem source_packet_vertex_integral (μ : Measure X)
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hwint : ∀ t ∈ tops, Integrable (weight t) μ)
    (hwmeas : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ q, Measurable (fun x => value x q)) (phase : ℕ → ℂ) (a α p : ℝ)
    {Kb : ℕ} (hKb : 0 < Kb) (shift : Fin Kb) (count : ℕ) (cell : ℤ)
    (M C P : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) (hα : 1 ≤ α) (hp0 : 0 ≤ p)
    (good : Set X) (hgood : MeasurableSet good) (bad : τ → Set X)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ x ∈ good, ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (hbad : ∀ x ∈ good, (1+C^p*(M+1)^(α-1))*
      (∑ t ∈ (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).filter
        (fun t => x ∈ bad t), weight t x) ≤ 1/2)
    (hpathInt : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      Integrable ((good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x)) μ)
    (hpathBound : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      (∫ x, (good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x) x ∂μ) ≤ P*∫ x, weight t x ∂μ) :
    let V := fun x => vertexAmount
      (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell) α p
    Integrable (good.indicator V) μ ∧
      (∫ x, good.indicator V x ∂μ) ≤
        (1+C^p*(M+1)^(α-1))*(1+2*P)*
          ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
            ∫ x, weight t x ∂μ := by
  intro V
  let R := g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell
  let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell
  let cost := 1+C^p*(M+1)^(α-1)
  let f := fun t => (good\bad t).indicator (fun x => weight t x*
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M shift t count x)
  have hcost : 0 ≤ cost := by dsimp [cost]; positivity
  have hRtop {t : τ} (ht : t ∈ R) : t ∈ tops := (g.mem_cellTops _ _ _ _ _ _ _).mp ht |>.1
  have hnint : Integrable n μ := integrable_finsetSum R (fun t ht => hwint t (hRtop ht))
  have hn0 (x : X) : 0 ≤ n x := g.mass_nonnegative tops slope precision cutoff weight
    (fun t x => (hw t x).le) _ _ x
  have hfn (t : τ) (ht : t ∈ R) : Integrable (f t) μ := hpathInt t ht
  have hsumInt : Integrable (fun x => ∑ t ∈ R, f t x) μ := integrable_finsetSum R hfn
  have hVmeas : Measurable V := by
    have hn := g.measurable_mass tops slope precision cutoff weight hwmeas
      (ShiftedBlocks.endpoint shift 0) cell
    have hA := g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas
      K gap packets assigned stop value hv phase a (ShiftedBlocks.endpoint shift 0) cell
    dsimp only [V,vertexAmount]
    fun_prop
  have hV0 (x : X) : 0 ≤ V x := by
    dsimp only [V,vertexAmount]
    exact add_nonneg (hn0 x) (mul_nonneg (Real.rpow_nonneg (hn0 x) _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hpoint (x : X) : good.indicator V x ≤
      cost*good.indicator n x+2*cost*∑ t ∈ R, f t x := by
    by_cases hx : x ∈ good
    · have h := g.sourceTree_packet_vertex_bound tops slope precision cutoff weight K gap
        packets assigned stop value phase a α p shift x hp hw hKb count cell M C hM hC hα hp0
        hne hterminal (henvelope x hx) (R.filter (fun t => x ∈ bad t))
        (Finset.filter_subset ..) (hbad x hx)
      have hs : (∑ t ∈ R\R.filter (fun t => x ∈ bad t), weight t x*
          g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
            phase a α p M shift t count x) = ∑ t ∈ R, f t x := by
        rw [Finset.sdiff_eq_filter,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hb : x ∈ bad t <;> simp [f,ht,hb,hx]
      rw [hs] at h
      simpa only [Set.indicator_of_mem hx] using h
    · have hfzero (t : τ) : f t x = 0 := Set.indicator_of_notMem (fun h => hx h.1) _
      simp only [Set.indicator_of_notMem hx,hfzero,Finset.sum_const_zero,mul_zero,add_zero,le_refl]
  have hnG := hnint.indicator hgood
  have hmajor := (hnG.const_mul cost).add (hsumInt.const_mul (2*cost))
  have hVint : Integrable (good.indicator V) μ := hmajor.mono'
    (hVmeas.indicator hgood).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Set.indicator_nonneg (fun x _ => hV0 x) x)]
      exact hpoint x)
  have hnBound : (∫ x, good.indicator n x ∂μ) ≤ ∑ t ∈ R, ∫ x, weight t x ∂μ := by
    have hi := integral_mono hnG hnint (fun x => by
      by_cases hx : x ∈ good
      · simp only [Set.indicator_of_mem hx,le_refl]
      · simpa only [Set.indicator_of_notMem hx] using hn0 x)
    have heq : (∫ x, n x ∂μ) = ∑ t ∈ R, ∫ x, weight t x ∂μ :=
      integral_finsetSum R (fun t ht => hwint t (hRtop ht))
    exact hi.trans_eq heq
  have hfBound : (∫ x, ∑ t ∈ R, f t x ∂μ) ≤ P*∑ t ∈ R, ∫ x, weight t x ∂μ := by
    rw [integral_finsetSum R hfn,Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => hpathBound t ht
  refine ⟨hVint,?_⟩
  calc
    _ ≤ ∫ x, cost*good.indicator n x+2*cost*∑ t ∈ R, f t x ∂μ :=
      integral_mono hVint hmajor hpoint
    _ = cost*(∫ x, good.indicator n x ∂μ)+2*cost*(∫ x, ∑ t ∈ R, f t x ∂μ) := by
      rw [integral_add (hnG.const_mul cost) (hsumInt.const_mul (2*cost)),
        integral_const_mul,integral_const_mul]
    _ ≤ cost*(∑ t ∈ R, ∫ x, weight t x ∂μ)+
        2*cost*(P*∑ t ∈ R, ∫ x, weight t x ∂μ) := add_le_add
      (mul_le_mul_of_nonneg_left hnBound hcost)
      (mul_le_mul_of_nonneg_left hfBound (by positivity))
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeVertexMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite packet-tree estimate yields the normalized root
Lp moment on the common good set, with no abstract terminal flow input. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ] [MeasurableSpace X]

theorem source_packet_vertex_moment (μ : Measure X)
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hwint : ∀ t ∈ tops, Integrable (weight t) μ)
    (hwmeas : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ q, Measurable (fun x => value x q)) (phase : ℕ → ℂ) (a α p : ℝ)
    {Kb : ℕ} (hKb : 0 < Kb) (shift : Fin Kb) (count : ℕ) (cell : ℤ)
    (M C P : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) (hα : 1 ≤ α) (hp0 : 0 < p)
    (good : Set X) (hgood : MeasurableSet good) (bad : τ → Set X)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ x ∈ good, ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (hbad : ∀ x ∈ good, (1+C^p*(M+1)^(α-1))*
      (∑ t ∈ (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).filter
        (fun t => x ∈ bad t), weight t x) ≤ 1/2)
    (hpathInt : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      Integrable ((good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x)) μ)
    (hpathBound : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      (∫ x, (good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x) x ∂μ) ≤ P*∫ x, weight t x ∂μ) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell
    let amp := fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell
    IntegrableOn (fun x => ‖(n x^(α/p-1)) • amp x‖^p) good μ ∧
      (∫ x in good, ‖(n x^(α/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
        ((1+C^p*(M+1)^(α-1))*(1+2*P)*
          ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
            ∫ x, weight t x ∂μ)^(1/p) := by
  intro n amp
  have hvertex := g.source_packet_vertex_integral μ tops slope precision cutoff weight hp hw
    hwint hwmeas K gap packets assigned stop value hv phase a α p hKb shift count cell
    M C P hM hC hα hp0.le good hgood bad hne hterminal henvelope hbad hpathInt hpathBound
  let R := g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell
  have hn : ∀ x, 0 < n x := by
    intro x
    obtain ⟨t,ht⟩ := hne
    exact g.mass_pos_of_member tops slope precision cutoff weight hw
      (ShiftedBlocks.endpoint shift 0) cell x ht
  have hnint : Integrable n μ := integrable_finsetSum R (fun t ht =>
    hwint t ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1)
  have hvi : Integrable (fun x => vertexAmount (n x) (amp x) α p) (μ.restrict good) :=
    (integrable_indicator_iff hgood).mp hvertex.1
  have hvb : (∫ x, vertexAmount (n x) (amp x) α p ∂μ.restrict good) ≤
      (1+C^p*(M+1)^(α-1))*(1+2*P)*∑ t ∈ R, ∫ x, weight t x ∂μ := by
    rw [← integral_indicator hgood]
    exact hvertex.2
  exact ⟨normalized_vertex_energy_integrable (μ.restrict good) n amp hn hp0.ne'
      hnint.restrict hvi,
    normalized_vertex_moment_le (μ.restrict good) n amp hn hp0 hnint.restrict hvi hvb⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundedDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Hilbert-valued tests recover the Lp norm on each finite
exhaustion set used in the source interpolation. The canonical test is
constructed explicitly and introduces no dimension-dependent constant. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

omit [MeasurableSpace X] in
theorem sourceCanonicalDual_norm (F : X → EuclideanSpace ℂ κ) {p : ℝ}
    (hp : 1 < p) (x : X) : ‖sourceCanonicalDual F p x‖ = ‖F x‖^(p-1) := by
  rw [sourceCanonicalDual,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hzero : F x = 0
  · simp [hzero,Real.zero_rpow (show p-1 ≠ 0 by linarith)]
  · calc
      _ = ‖F x‖^(p-2)*‖F x‖^(1:ℝ) := by rw [Real.rpow_one]
      _ = ‖F x‖^(p-1) := by rw [← Real.rpow_add (norm_pos_iff.mpr hzero)]; congr 1; ring

omit [MeasurableSpace X] in
theorem sourceCanonicalDual_pairing (F : X → EuclideanSpace ℂ κ) {p : ℝ}
    (hp : 1 < p) (x : X) :
    ⟪sourceCanonicalDual F p x,F x⟫_ℂ = (‖F x‖^p:ℝ) := by
  have heq : ‖F x‖^(p-2)*‖F x‖^2 = ‖F x‖^p := by
    by_cases hzero : F x = 0
    · simp [hzero,Real.zero_rpow (show p ≠ 0 by linarith)]
    · rw [← Real.rpow_natCast,← Real.rpow_add (norm_pos_iff.mpr hzero)]
      congr 1
      push_cast
      ring
  rw [sourceCanonicalDual,inner_smul_left,Complex.conj_ofReal]
  have hre : (⟪F x,F x⟫_ℂ).re = ‖F x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (F x)
  have him : (⟪F x,F x⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (F x)
  apply Complex.ext
  · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,hre,zero_mul,sub_zero] using heq
  · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,him,mul_zero,zero_mul,add_zero]

theorem source_bounded_lp_of_dual_tests (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → EuclideanSpace ℂ κ) (hF : Measurable F) (A C p : ℝ)
    (hC : 0 ≤ C) (hp : 1 < p) (hbound : ∀ x, ‖F x‖ ≤ A)
    (htest : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) →
      ‖∫ x, ⟪b x,F x⟫_ℂ ∂μ‖ ≤ C*(∫ x, ‖b x‖^(p/(p-1)) ∂μ)^(1/(p/(p-1)))) :
    (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ C := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-1 := by linarith
  have hDmeas : Measurable (sourceCanonicalDual F p) :=
    ((hF.norm.pow_const _).complex_ofReal).smul hF
  have hDbound : ∀ x, ‖sourceCanonicalDual F p x‖ ≤ A^(p-1) := by
    intro x
    rw [sourceCanonicalDual_norm F hp]
    exact Real.rpow_le_rpow (norm_nonneg _) (hbound x) hpm.le
  have h := htest (sourceCanonicalDual F p) hDmeas ⟨A^(p-1),hDbound⟩
  have hpair : (∫ x, ⟪sourceCanonicalDual F p x,F x⟫_ℂ ∂μ) =
      ((∫ x, ‖F x‖^p ∂μ):ℝ) := by
    simp_rw [sourceCanonicalDual_pairing F hp]
    exact integral_complex_ofReal
  have hpow (x : X) : ‖sourceCanonicalDual F p x‖^(p/(p-1)) = ‖F x‖^p := by
    rw [sourceCanonicalDual_norm F hp,← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  have hI0 : 0 ≤ ∫ x, ‖F x‖^p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [hpair,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hI0] at h
  simp_rw [hpow] at h
  by_cases hz : (∫ x, ‖F x‖^p ∂μ) = 0
  · simpa only [hz,Real.zero_rpow (one_div_ne_zero hp0.ne')] using hC
  · have hi : 0 < ∫ x, ‖F x‖^p ∂μ := lt_of_le_of_ne hI0 (Ne.symm hz)
    have hdiv := (div_le_iff₀ (Real.rpow_pos_of_pos hi (1/(p/(p-1))))).mpr h
    have heq : (∫ x, ‖F x‖^p ∂μ)/(∫ x, ‖F x‖^p ∂μ)^(1/(p/(p-1))) =
        (∫ x, ‖F x‖^p ∂μ)^(1/p) := by
      calc
        _ = (∫ x, ‖F x‖^p ∂μ)^(1:ℝ)/(∫ x, ‖F x‖^p ∂μ)^(1/(p/(p-1))) := by rw [Real.rpow_one]
        _ = (∫ x, ‖F x‖^p ∂μ)^(1-1/(p/(p-1))) := (Real.rpow_sub hi _ _).symm
        _ = _ := by congr 1; field_simp; ring
    exact heq ▸ hdiv

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSimplexLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar damped simplex theorem gives a dimension-independent Lp
estimate on each bounded exhaustion of the actual packet family. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem damped_simplex_barycenter_nonneg [DecidableEq ι] [Nonempty ι]
    (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ)) (hD : Convex ℝ D)
    (C mu : ℝ) (hC : 0 ≤ C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) M a)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) C (Pi.single i mu)) :
    ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))‖ ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply damped_simplex_barycenter F D hD (C+ε) mu (by linarith)
    hentire hbounded hvertices
  intro i eta
  exact (hvertex i eta).trans (le_add_of_nonneg_right hε.le)

theorem source_bounded_pairing_bound (μ : Measure X) [IsFiniteMeasure μ]
    (F b : X → EuclideanSpace ℂ κ) (hF : Measurable F) (hb : Measurable b)
    (A B p : ℝ) (hp : 1 < p) (hFA : ∀ x, ‖F x‖ ≤ A) (hbB : ∀ x, ‖b x‖ ≤ B) :
    ‖∫ x, ⟪b x,F x⟫_ℂ ∂μ‖ ≤
      (∫ x, ‖F x‖^p ∂μ)^(1/p)*(∫ x, ‖b x‖^(p/(p-1)) ∂μ)^(1/(p/(p-1))) := by
  have hFp : MemLp F (ENNReal.ofReal p) μ :=
    MemLp.of_bound hF.aestronglyMeasurable A (Filter.Eventually.of_forall hFA)
  have hbp : MemLp b (ENNReal.ofReal (p/(p-1))) μ :=
    MemLp.of_bound hb.aestronglyMeasurable B (Filter.Eventually.of_forall hbB)
  have hprod : Integrable (fun x => ‖F x‖*‖b x‖) μ := by
    apply (integrable_const (|A| * |B|)).mono' (hF.norm.mul hb.norm).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖‖F x‖*‖b x‖‖ ≤ |A| * |B|
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul ((hFA x).trans (le_abs_self A)) ((hbB x).trans (le_abs_self B))
      (norm_nonneg _) (abs_nonneg _)
  calc
    _ ≤ ∫ x, ‖⟪b x,F x⟫_ℂ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖F x‖*‖b x‖ ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hprod
      exact Filter.Eventually.of_forall fun x => by
        simpa only [mul_comm] using norm_inner_le_norm (b x) (F x)
    _ ≤ _ := integral_mul_norm_le_Lp_mul_Lq (Real.HolderConjugate.conjExponent hp) hFp hbp

theorem source_simplex_lp_of_bounded_integrals [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : (ι → ℂ) → X → EuclideanSpace ℂ κ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (p C mu : ℝ) (hp : 1 < p) (hC : 0 ≤ C)
    (hF : ∀ z, Measurable (F z)) (hFbound : ∀ z, ∃ A : ℝ, ∀ x, ‖F z x‖ ≤ A)
    (hentire : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x, ⟪b x,F (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, ∀ eta x,
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • F (phaseTubePoint a eta) x‖ ≤ M)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    (∫ x, ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0)) x‖^p ∂μ)^(1/p) ≤ C := by
  obtain ⟨A,hA⟩ := hFbound (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
  apply source_bounded_lp_of_dual_tests μ _ (hF _) A C p hC hp hA
  intro b hb hbB
  obtain ⟨B,hB⟩ := hbB
  let t := (∫ x, ‖b x‖^(p/(p-1)) ∂μ)^(1/(p/(p-1)))
  have ht : 0 ≤ t := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  let phi := fun z => ∫ x, ⟪b x,F z x⟫_ℂ ∂μ
  have hscale (z : ι → ℂ) : gaussianPhaseDamping z*phi z =
      ∫ x, ⟪b x,gaussianPhaseDamping z • F z x⟫_ℂ ∂μ := by
    simp_rw [inner_smul_right]
    exact (integral_const_mul _ _).symm
  refine damped_simplex_barycenter_nonneg phi D hD (C*t) mu (mul_nonneg hC ht)
    (hentire b hb ⟨B,hB⟩) ?_ hvertices ?_
  · obtain ⟨M,hM⟩ := hbounded
    refine ⟨(|B| * M)*μ.real univ,?_⟩
    intro a ha eta
    dsimp only
    rw [hscale]
    apply norm_integral_le_of_norm_le_const
    exact Filter.Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul ((hB x).trans (le_abs_self _)) (hM a ha eta x)
        (norm_nonneg _) (abs_nonneg _))
  · intro i eta
    dsimp only
    rw [hscale]
    let z := phaseTubePoint (Pi.single i mu) eta
    obtain ⟨V,hV⟩ := hFbound z
    have hG : Measurable (fun x => gaussianPhaseDamping z • F z x) := by
      exact (measurable_const : Measurable (fun _ : X => gaussianPhaseDamping z)).smul (hF z)
    have hGV : ∀ x, ‖gaussianPhaseDamping z • F z x‖ ≤ ‖gaussianPhaseDamping z‖*V := by
      intro x
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hV x) (norm_nonneg _)
    exact (source_bounded_pairing_bound μ _ b hG hb _ B p hp hGV hB).trans
      (mul_le_mul_of_nonneg_right (hvertex i eta) ht)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLpExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded logarithmic-coefficient exhaustions preserve the uniform
Lp estimate. Integrability of the full power is proved by monotone
Lebesgue integration, before passing back to the real integral. -/

noncomputable section
open MeasureTheory Set Filter
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem sourceExhaustion_measurable (R : X → ℝ) (hR : Measurable R) (n : ℕ) :
    MeasurableSet (sourceExhaustion R n) := measurableSet_le hR measurable_const

omit [MeasurableSpace X] in
theorem sourceExhaustion_mono (R : X → ℝ) : Monotone (sourceExhaustion R) := by
  intro n m hnm x hx
  change R x ≤ (n:ℝ) at hx
  change R x ≤ (m:ℝ)
  exact hx.trans (by exact_mod_cast hnm)

omit [MeasurableSpace X] in
theorem sourceExhaustion_covers (R : X → ℝ) : (⋃ n, sourceExhaustion R n) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n,hn⟩ := exists_nat_ge (R x)
  exact mem_iUnion.mpr ⟨n,hn⟩

theorem source_lp_of_exhaustion (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
    (hF : Measurable F) (p C : ℝ) (hp : 0 < p) (hC : 0 ≤ C)
    (A : ℕ → Set X) (hmono : Monotone A)
    (hcover : (⋃ n, A n) = univ)
    (henergy : ∀ n, IntegrableOn (fun x => ‖F x‖^p) (A n) μ)
    (hbound : ∀ n, (∫ x in A n, ‖F x‖^p ∂μ)^(1/p) ≤ C) :
    Integrable (fun x => ‖F x‖^p) μ ∧ (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ C := by
  have hnonneg (x : X) : 0 ≤ ‖F x‖^p := Real.rpow_nonneg (norm_nonneg _) _
  have hpower (n : ℕ) : (∫ x in A n, ‖F x‖^p ∂μ) ≤ C^p := by
    have hI : 0 ≤ ∫ x in A n, ‖F x‖^p ∂μ := integral_nonneg hnonneg
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hI (1/p)) (hbound n) hp.le
    rw [← Real.rpow_mul hI,one_div_mul_cancel hp.ne',Real.rpow_one] at h
    exact h
  have hlin : (∫⁻ x, ENNReal.ofReal (‖F x‖^p) ∂μ) ≤ ENNReal.ofReal (C^p) := by
    have hi := setLIntegral_iUnion_of_directed (μ := μ)
      (fun x => ENNReal.ofReal (‖F x‖^p)) hmono.directed_le
    rw [hcover,Measure.restrict_univ] at hi
    rw [hi]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (henergy n) (Eventually.of_forall hnonneg)]
    exact ENNReal.ofReal_le_ofReal (hpower n)
  have hint : Integrable (fun x => ‖F x‖^p) μ := by
    refine ⟨(hF.norm.pow_const p).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnonneg)).mpr
      (hlin.trans_lt ENNReal.ofReal_lt_top)
  have hglobal : (∫ x, ‖F x‖^p ∂μ) ≤ C^p := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnonneg)] at hlin
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hC _)).mp hlin
  refine ⟨hint,?_⟩
  have h := Real.rpow_le_rpow (integral_nonneg hnonneg) hglobal (one_div_pos.mpr hp).le
  rwa [← Real.rpow_mul hC,mul_one_div_cancel hp.ne',Real.rpow_one] at h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single exhaustion, independent of the complex phase, bounds all
original packet bases and the absolute logarithms along their paths. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

omit [MeasurableSpace X] [Fintype κ] in
theorem pathLogSize_nonneg (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (lower upper : ℕ) (slope : ℝ) : 0 ≤ g.pathLogSize mass boundary lower upper slope :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [MeasurableSpace X] [Fintype κ] in
theorem pathLogCombination_norm_le (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (slope : ℝ) :
    ‖g.pathLogCombination mass boundary phase lower upper slope‖ ≤
      (∑ j ∈ Finset.Ico lower upper, ‖phase j‖)*g.pathLogSize mass boundary lower upper slope := by
  unfold pathLogCombination pathLogSize
  calc
    _ ≤ ∑ j ∈ Finset.Ico lower upper,
        ‖phase j*(Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope)):ℂ)‖ :=
      norm_sum_le _ _
    _ = ∑ j ∈ Finset.Ico lower upper, ‖phase j‖*
        |Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope))| := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ ∑ j ∈ Finset.Ico lower upper, (∑ k ∈ Finset.Ico lower upper, ‖phase k‖)*
        |Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope))| := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => norm_nonneg (phase k)) hj) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem measurable_sourceAmplitudeRadius (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (a : ℝ) (level : ℕ) (cell : ℤ) :
    Measurable (g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell) := by
  unfold sourceAmplitudeRadius
  apply Finset.measurable_sum
  intro s _
  apply (g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s).norm.add
  unfold pathLogSize
  apply Finset.measurable_sum
  intro j _
  simpa only [Real.norm_eq_abs,Pi.div_apply] using ((g.measurable_mass tops slope precision cutoff weight hw _ _).div
    (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap _ _)).log.norm

omit [MeasurableSpace X] in
theorem sourceAmplitudeRadius_base_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (s : σ) (hs : s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell) (x : X) :
    ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ ≤
      g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell x := by
  unfold sourceAmplitudeRadius
  let B := fun t => ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x t‖
  let Q := fun t => g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
    level (stop t) (slope (assigned t))
  have hQ (t : σ) : 0 ≤ Q t := g.pathLogSize_nonneg _ _ _ _ _
  change B s ≤ ∑ t ∈ g.packetSet packets (fun t => slope (assigned t)) stop level cell, (B t+Q t)
  exact (le_add_of_nonneg_right (hQ s)).trans (Finset.single_le_sum
    (fun t _ => add_nonneg (norm_nonneg _) (hQ t)) hs)

omit [MeasurableSpace X] in
theorem sourceAmplitudeRadius_log_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (s : σ) (hs : s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell) (x : X) :
    g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
        (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
        level (stop s) (slope (assigned s)) ≤
      g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell x := by
  unfold sourceAmplitudeRadius
  let B := fun t => ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x t‖
  let Q := fun t => g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
    level (stop t) (slope (assigned t))
  have hB (t : σ) : 0 ≤ B t := norm_nonneg _
  have hQ (t : σ) : 0 ≤ Q t := g.pathLogSize_nonneg _ _ _ _ _
  change Q s ≤ ∑ t ∈ g.packetSet packets (fun t => slope (assigned t)) stop level cell, (B t+Q t)
  exact (le_add_of_nonneg_left (hB s)).trans (Finset.single_le_sum
    (fun t _ => add_nonneg (hB t) (hQ t)) hs)

theorem sourcePacketAmplitude_integral_entire_on_exhaustion
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (a : ℝ) (level : ℕ) (cell : ℤ) (n : ℕ) (offset direction : ℕ → ℂ)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b) (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x in sourceExhaustion
      (g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell) n,
      ⟪b x,g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (fun j => offset j+z*direction j) a x level cell⟫_ℂ ∂μ) := by
  let R := g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell
  let P := fun (phase : ℕ → ℂ) (s : σ) => ∑ j ∈ Finset.Ico level (stop s), ‖phase j‖
  have hP (phase : ℕ → ℂ) (s : σ) : 0 ≤ P phase s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlog (phase : ℕ → ℂ) (s : σ)
      (hs : s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell)
      (x : X) (hx : x ∈ sourceExhaustion R n) :
      ‖g.sourcePathLog tops slope precision cutoff weight K gap phase level (stop s)
        (slope (assigned s)) x‖ ≤ P phase s*(n:ℝ) := by
    apply (g.pathLogCombination_norm_le _ _ phase level (stop s) (slope (assigned s))).trans
    apply mul_le_mul_of_nonneg_left _ (hP phase s)
    exact (g.sourceAmplitudeRadius_log_le tops slope precision cutoff weight K gap packets
      assigned stop value a level cell s hs x).trans hx
  apply g.sourcePacketAmplitude_integral_affine_entire_on μ tops slope precision cutoff weight hw
    K gap packets assigned stop value hv offset direction a level cell (sourceExhaustion R n)
    (sourceExhaustion_measurable R (g.measurable_sourceAmplitudeRadius tops slope precision cutoff
      weight hw K gap packets assigned stop value hv a level cell) n)
    (fun _ => (n:ℝ)) (fun s => (P offset s+P direction s)*(n:ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun s _ => mul_nonneg (add_nonneg (hP offset s) (hP direction s)) (Nat.cast_nonneg _))
    _ _ _ b hb T hbT
  · intro s hs x hx
    exact (g.sourceAmplitudeRadius_base_le tops slope precision cutoff weight K gap packets
      assigned stop value a level cell s hs x).trans hx
  · intro s hs x hx
    exact (hlog offset s hs x hx).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hP direction s)) (Nat.cast_nonneg _))
  · intro s hs x hx
    exact (hlog direction s hs x hx).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hP offset s)) (Nat.cast_nonneg _))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On each fixed exhaustion the original source amplitude is bounded
for every complex phase. Nonnegative real phases give the sharper
phase-independent bound needed on the simplex tube. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [Fintype κ]

theorem sourcePacketAmplitude_norm_on_exhaustion (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (phase : ℕ → ℂ) (n : ℕ) (x : X)
    (hx : x ∈ sourceExhaustion (g.sourceAmplitudeRadius tops slope precision cutoff weight K gap
      packets assigned stop value a level cell) n) :
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) phase a x level cell‖ ≤
      ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
        Real.exp ((∑ j ∈ Finset.Ico level (stop s), ‖phase j‖)*(n:ℝ))*(n:ℝ) := by
  have heq := g.sourcePacketAmplitude_affine_exp tops slope precision cutoff weight K gap packets
    assigned stop (value x) phase (fun _ => 0) a x level cell (0:ℂ)
  simp only [zero_mul,add_zero] at heq
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_smul]
  have hbase : ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ ≤ (n:ℝ) :=
    (g.sourceAmplitudeRadius_base_le tops slope precision cutoff weight K gap packets assigned stop
      value a level cell s hs x).trans hx
  have hlog : ‖g.sourcePathLog tops slope precision cutoff weight K gap phase level (stop s)
      (slope (assigned s)) x‖ ≤ (∑ j ∈ Finset.Ico level (stop s), ‖phase j‖)*(n:ℝ) := by
    apply (g.pathLogCombination_norm_le _ _ phase level (stop s) (slope (assigned s))).trans
    exact mul_le_mul_of_nonneg_left
      ((g.sourceAmplitudeRadius_log_le tops slope precision cutoff weight K gap packets assigned stop
        value a level cell s hs x).trans hx) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hexp : ‖Complex.exp (g.sourcePathLog tops slope precision cutoff weight K gap phase level
      (stop s) (slope (assigned s)) x)‖ ≤
      Real.exp ((∑ j ∈ Finset.Ico level (stop s), ‖phase j‖)*(n:ℝ)) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hlog)
  exact mul_le_mul hexp hbase (norm_nonneg _) (Real.exp_pos _).le

theorem sourcePacketAmplitude_norm_le_radius (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (phase : ℕ → ℂ) (hphase : ∀ j, 0 ≤ (phase j).re) (x : X) :
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) phase a x level cell‖ ≤
      g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell x := by
  unfold sourcePacketAmplitude packetAmplitude sourceAmplitudeRadius
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  have hsp : s ∈ packets := (Finset.mem_filter.mp hs).1
  have ht := hassigned s hsp
  have hprod : ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      level (stop s) (slope (assigned s))‖ ≤ 1 := by
    rw [packetPathProduct,norm_prod]
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro j hj
    have hjstop : j+1 ≤ stop s := by have := (Finset.mem_Ico.mp hj).2; omega
    exact g.sourceTransition_norm_le_one tops slope precision cutoff weight hp hw hK gap phase x j
      (assigned s) ht (g.eligible_of_le (hp _ ht) hjstop (heligible s hsp)) (hphase j)
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hprod).trans
    (le_add_of_nonneg_right (g.pathLogSize_nonneg _ _ _ _ _))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSimplexLpOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted-set form of the bounded simplex estimate. The zero
extension supplies bounded tests on the ambient finite measure space. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem source_integral_inner_indicator (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (F b : X → EuclideanSpace ℂ κ) :
    (∫ x, ⟪b x,A.indicator F x⟫_ℂ ∂μ) = ∫ x in A, ⟪b x,F x⟫_ℂ ∂μ := by
  classical
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ A <;> simp [hx]

theorem source_integral_norm_indicator_power (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (F : X → EuclideanSpace ℂ κ) (c : ℂ) (p : ℝ) (hp : p ≠ 0) :
    (∫ x, ‖c • A.indicator F x‖^p ∂μ) = ∫ x in A, ‖c • F x‖^p ∂μ := by
  classical
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ A <;> simp [hx,Real.zero_rpow hp]

theorem source_simplex_lp_on [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : MeasurableSet A)
    (F : (ι → ℂ) → X → EuclideanSpace ℂ κ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (p C mu : ℝ) (hp : 1 < p) (hC : 0 ≤ C)
    (hF : ∀ z, Measurable (F z)) (hFbound : ∀ z, ∃ V : ℝ, ∀ x ∈ A, ‖F z x‖ ≤ V)
    (hentire : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x in A, ⟪b x,F (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, ∀ eta x, x ∈ A →
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • F (phaseTubePoint a eta) x‖ ≤ M)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x in A, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    (∫ x in A, ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0)) x‖^p ∂μ)^(1/p) ≤ C := by
  classical
  let G := fun z => A.indicator (F z)
  have hG : ∀ z, Measurable (G z) := fun z => (hF z).indicator hA
  have hGb : ∀ z, ∃ V : ℝ, ∀ x, ‖G z x‖ ≤ V := by
    intro z
    obtain ⟨V,hV⟩ := hFbound z
    refine ⟨|V|,?_⟩
    intro x
    by_cases hx : x ∈ A
    · have hz : ‖G z x‖ ≤ V := by simpa only [G,indicator_of_mem hx] using hV x hx
      exact hz.trans (le_abs_self _)
    · simpa only [G,indicator_of_notMem hx,norm_zero] using abs_nonneg V
  have he : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x, ⟪b x,G (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ) := by
    intro b hb hbB a ha a' ha' eta
    simp_rw [G,source_integral_inner_indicator μ A hA]
    exact hentire b hb hbB a ha a' ha' eta
  have hbd : ∃ M : ℝ, ∀ a ∈ D, ∀ eta x,
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • G (phaseTubePoint a eta) x‖ ≤ M := by
    obtain ⟨M,hM⟩ := hbounded
    refine ⟨|M|,?_⟩
    intro a ha eta x
    by_cases hx : x ∈ A
    · have hz : ‖gaussianPhaseDamping (phaseTubePoint a eta) • G (phaseTubePoint a eta) x‖ ≤ M := by
        simpa only [G,indicator_of_mem hx] using hM a ha eta x hx
      exact hz.trans (le_abs_self _)
    · simpa only [G,indicator_of_notMem hx,smul_zero,norm_zero] using abs_nonneg M
  have hv : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        G (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C := by
    intro i eta
    rw [source_integral_norm_indicator_power μ A hA _ _ _ (by linarith)]
    exact hvertex i eta
  have h := source_simplex_lp_of_bounded_integrals μ G D hD p C mu hp hC hG hGb he hbd hvertices hv
  have hi := source_integral_norm_indicator_power μ A hA
    (F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))) (1:ℂ) p (by linarith)
  simp only [one_smul] at hi
  change (∫ x, ‖A.indicator (F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))) x‖^p ∂μ)^(1/p) ≤ C at h
  rwa [hi] at h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSimplexLpExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vertex moments imply the full diagonal Lp estimate once
bounded analytic exhaustions have been constructed. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem source_simplex_lp_of_exhaustions [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A) (hcover : (⋃ n, A n) = univ)
    (F : (ι → ℂ) → X → EuclideanSpace ℂ κ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (p C mu : ℝ) (hp : 1 < p) (hC : 0 ≤ C)
    (hF : ∀ z, Measurable (F z))
    (hFbound : ∀ n z, ∃ V : ℝ, ∀ x ∈ A n, ‖F z x‖ ≤ V)
    (hentire : ∀ n, ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x in A n, ⟪b x,F (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ))
    (hbounded : ∀ n, ∃ M : ℝ, ∀ a ∈ D, ∀ eta x, x ∈ A n →
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • F (phaseTubePoint a eta) x‖ ≤ M)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvint : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    let central := F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    Integrable (fun x => ‖central x‖^p) μ ∧ (∫ x, ‖central x‖^p ∂μ)^(1/p) ≤ C := by
  intro central
  have hp0 : 0 < p := by linarith
  apply source_lp_of_exhaustion μ central (hF _) p C hp0 hC A hmono hcover
  · intro n
    obtain ⟨V,hV⟩ := hFbound n (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    apply (integrable_const (|V|^p)).mono' ((hF _).norm.pow_const p).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (hA n)] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) ((hV x hx).trans (le_abs_self _)) hp0.le
  · intro n
    apply source_simplex_lp_on μ (A n) (hA n) F D hD p C mu hp hC hF
      (hFbound n) (hentire n) (hbounded n) hvertices
    intro i eta
    apply le_trans (Real.rpow_le_rpow
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
      (integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _) (hvint i eta))
      (one_div_pos.mpr hp0).le)
    exact hvertex i eta

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAmplitudeInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original source family satisfies the analytic simplex estimate.
Only its vertex moments remain as input; measurability, analytic slices,
bounded exhaustion, and the full-set limiting argument are proved here. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem sourceShiftFamily_diagonal_lp [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwmeas : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (phaseIndex : ℕ → ι) (a : ℝ) (level : ℕ) (cell : ℤ)
    (D : Set (ι → ℝ)) (hD : Convex ℝ D) (B p C mu : ℝ)
    (hDpos : ∀ v ∈ D, ∀ i, 0 ≤ v i) (hDsq : ∀ v ∈ D, (∑ i, (v i)^2) ≤ B)
    (hp1 : 1 < p) (hC : 0 ≤ C) (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvint : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    let central := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      value phaseIndex a level cell (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    Integrable (fun x => ‖central x‖^p) μ ∧ (∫ x, ‖central x‖^p ∂μ)^(1/p) ≤ C := by
  let F := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
    phaseIndex a level cell
  let R := g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell
  have hR := g.measurable_sourceAmplitudeRadius tops slope precision cutoff weight hwmeas K gap
    packets assigned stop value hv a level cell
  apply source_simplex_lp_of_exhaustions μ (sourceExhaustion R)
    (sourceExhaustion_measurable R hR) (sourceExhaustion_mono R) (sourceExhaustion_covers R)
    F D hD p C mu hp1 hC
  · intro z
    exact g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas K gap
      packets assigned stop value hv (fun j => z (phaseIndex j)) a level cell
  · intro n z
    refine ⟨∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
      Real.exp ((∑ j ∈ Finset.Ico level (stop s), ‖z (phaseIndex j)‖)*(n:ℝ))*(n:ℝ),?_⟩
    intro x hx
    exact g.sourcePacketAmplitude_norm_on_exhaustion tops slope precision cutoff weight K gap
      packets assigned stop value a level cell (fun j => z (phaseIndex j)) n x hx
  · intro n b hb hbB v _ v' _ eta
    obtain ⟨T,hT⟩ := hbB
    let offset := fun j => (v (phaseIndex j):ℂ)+(eta (phaseIndex j):ℂ)*Complex.I
    let direction := fun j => (v' (phaseIndex j):ℂ)-(v (phaseIndex j):ℂ)
    have heq (z : ℂ) : (fun j => phaseTubeLine v v' eta z (phaseIndex j)) =
        (fun j => offset j+z*direction j) := by
      funext j
      dsimp only [phaseTubeLine,offset,direction]
      ring
    change Differentiable ℂ (fun z => ∫ x in sourceExhaustion R n,
      ⟪b x,g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (fun j => phaseTubeLine v v' eta z (phaseIndex j)) a x level cell⟫_ℂ ∂μ)
    simp_rw [heq]
    exact g.sourcePacketAmplitude_integral_entire_on_exhaustion μ tops slope precision cutoff weight
      hwmeas K gap packets assigned stop value hv a level cell n offset direction b hb T hT
  · intro n
    refine ⟨Real.exp B*(n:ℝ),?_⟩
    intro v hvD eta x hx
    have hf : ‖F (phaseTubePoint v eta) x‖ ≤ (n:ℝ) := by
      apply (g.sourcePacketAmplitude_norm_le_radius tops slope precision cutoff weight hp hw hK
        gap packets assigned stop value a level cell hassigned heligible
        (fun j => phaseTubePoint v eta (phaseIndex j)) _ x).trans hx
      intro j
      simpa [phaseTubePoint] using hDpos v hvD (phaseIndex j)
    have hd : ‖gaussianPhaseDamping (phaseTubePoint v eta)‖ ≤ Real.exp B := by
      rw [gaussianPhaseDamping_norm]
      apply Real.exp_le_exp.mpr
      exact (sub_le_self _ (Finset.sum_nonneg fun i _ => sq_nonneg (eta i))).trans (hDsq v hvD)
    rw [norm_smul]
    exact mul_le_mul hd hf (norm_nonneg _) (Real.exp_pos _).le
  · exact hvertices
  · exact hvint
  · exact hvertex

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCentralHolder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The central weight is controlled by the normalized vertex moment
and the measure of the common good set. This is the Hölder step in §11. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem central_weight_factorization {n alpha p beta : ℝ} (hn : 0 < n)
    (A : EuclideanSpace ℂ κ) :
    n^beta*‖A‖ = n^(1-alpha/p+beta)*‖(n^(alpha/p-1)) • A‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hn.le _),
    ← mul_assoc,← Real.rpow_add hn]
  congr 2
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCrudeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The linear node envelope gives the crude normalized moment on the
whole phase tube. Only the first power of the mass is integrated; its
remaining small power is controlled by the root mass bound. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem source_node_normalized_energy_le {n U C alpha p : ℝ}
    (A : EuclideanSpace ℂ κ) (hn : 0 < n) (hnU : n ≤ U)
    (hC : 0 ≤ C) (ha : 1 ≤ alpha) (hp : 0 < p) (hA : ‖A‖ ≤ C*n) :
    ‖(n^(alpha/p-1)) • A‖^p ≤ C^p*U^(alpha-1)*n := by
  rw [normalized_vertex_energy_eq hn hp.ne']
  calc
    _ ≤ n^(alpha-p)*(C*n)^p := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hA hp.le) (Real.rpow_nonneg hn.le _)
    _ = C^p*(n^(alpha-1)*n) := by
      rw [Real.mul_rpow hC hn.le]
      have hsum : n^(alpha-p)*n^p = n^alpha := by
        rw [← Real.rpow_add hn]
        congr 1
        ring
      have hsplit : n^(alpha-1)*n = n^alpha := by
        conv_lhs => rhs; rw [← Real.rpow_one n]
        rw [← Real.rpow_add hn]
        congr 1
        ring
      rw [hsplit]
      calc
        _ = C^p*(n^(alpha-p)*n^p) := by ring
        _ = _ := by rw [hsum]
    _ ≤ _ := by
      have hpow := Real.rpow_le_rpow hn.le hnU (sub_nonneg.mpr ha)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hC p)) hn.le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCrudeMomentAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-everywhere node and mass bounds suffice for normalized moments.
This lets the spatial measure be restricted to the common good set,
without adding bounds at points excluded by the construction. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem source_node_normalized_moment_ae (μ : Measure X)
    (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (U C alpha p : ℝ)
    (hn : ∀ x, 0 < n x) (hnU : ∀ᵐ x ∂μ, n x ≤ U) (hnmeas : Measurable n)
    (hnint : Integrable n μ) (hAmeas : Measurable A)
    (hU : 0 < U) (hC : 0 ≤ C) (ha : 1 ≤ alpha) (hp : 0 < p)
    (hA : ∀ᵐ x ∂μ, ‖A x‖ ≤ C*n x) :
    Integrable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • A x‖^p ∂μ)^(1/p) ≤
        C*U^((alpha-1)/p)*(∫ x, n x ∂μ)^(1/p) := by
  have hpoint : ∀ᵐ x ∂μ, ‖(n x^(alpha/p-1)) • A x‖^p ≤ C^p*U^(alpha-1)*n x := by
    filter_upwards [hnU,hA] with x hx hAx
    exact source_node_normalized_energy_le (A x) (hn x) hx hC ha hp hAx
  have hmeas : Measurable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) :=
    (((hnmeas.pow_const _).smul hAmeas).norm).pow_const _
  have hi : Integrable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) μ :=
    (hnint.const_mul (C^p*U^(alpha-1))).mono' hmeas.aestronglyMeasurable
      (by
        filter_upwards [hpoint] with x hx
        rwa [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])
  have hb : (∫ x, ‖(n x^(alpha/p-1)) • A x‖^p ∂μ) ≤
      C^p*U^(alpha-1)*(∫ x, n x ∂μ) := by
    simpa only [integral_const_mul] using integral_mono_ae hi
      (hnint.const_mul (C^p*U^(alpha-1))) hpoint
  refine ⟨hi,?_⟩
  apply (Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) hb
    (one_div_nonneg.mpr hp.le)).trans_eq
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg hU.le _))
      (integral_nonneg fun x => (hn x).le),
    Real.mul_rpow (Real.rpow_nonneg hC _) (Real.rpow_nonneg hU.le _),
    ← Real.rpow_mul hC,← Real.rpow_mul hU.le,mul_one_div_cancel hp.ne',Real.rpow_one]
  rw [show (alpha-1)*(1/p) = (alpha-1)/p by ring]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonnegative shift simplex and its vertex geometry. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem sourceShiftSimplex_convex (mu : ℝ) : Convex ℝ (sourceShiftSimplex (ι := ι) mu) := by
  intro a ha b hb r s hr hs hrs
  constructor
  · intro i
    exact add_nonneg (mul_nonneg hr (ha.1 i)) (mul_nonneg hs (hb.1 i))
  · change ∑ i, (r*a i+s*b i) = mu
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,ha.2,hb.2,← add_mul,hrs,one_mul]

theorem sourceShiftSimplex_sq_sum (mu : ℝ) (a : ι → ℝ)
    (ha : a ∈ sourceShiftSimplex mu) : (∑ i, (a i)^2) ≤ mu^2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := a) (fun i _ => ha.1 i)
  simpa only [ha.2] using h

theorem sourceShiftSimplex_vertex [DecidableEq ι] {mu : ℝ} (hmu : 0 ≤ mu) (i : ι) :
    Pi.single i mu ∈ sourceShiftSimplex mu := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j; simpa using hmu
    · simp [hji]
  · simp [Pi.single_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root-mass normalization is absorbed into the actual packet
values before interpolation. This identifies the interpolated family
with the normalized moments supplied by the packet tree. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

omit [MeasurableSpace X] [Fintype ι] in
theorem sourceShiftFamily_complex_weight (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phaseIndex : ℕ → ι)
    (a : ℝ) (level : ℕ) (cell : ℤ) (c : X → ℂ) (z : ι → ℂ) (x : X) :
    g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      (fun x s => c x • value x s) phaseIndex a level cell z x =
      c x • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
        value phaseIndex a level cell z x :=
  g.sourcePacketAmplitude_smul_value tops slope precision cutoff weight K gap packets assigned stop
    (value x) (fun j => z (phaseIndex j)) a x level cell (c x)

omit [MeasurableSpace X] [Fintype ι] in
theorem sourceShiftFamily_real_weight (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phaseIndex : ℕ → ι)
    (a : ℝ) (level : ℕ) (cell : ℤ) (c : X → ℝ) (z : ι → ℂ) (x : X) :
    g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      (fun x s => (c x:ℂ) • value x s) phaseIndex a level cell z x =
      c x • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
        value phaseIndex a level cell z x := by
  exact (g.sourceShiftFamily_complex_weight tops slope precision cutoff weight K gap packets assigned
    stop value phaseIndex a level cell (fun x => (c x:ℂ)) z x).trans
    (algebraMap_smul ℂ (c x) _)

theorem sourceShiftFamily_normalized_diagonal_lp [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwmeas : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (phaseIndex : ℕ → ι) (a : ℝ) (level : ℕ) (cell : ℤ)
    (n : X → ℝ) (hn : Measurable n) (r p C mu : ℝ)
    (hp1 : 1 < p) (hC : 0 ≤ C) (hmu : 0 ≤ mu)
    (hvint : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        ((n x^r) • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
          value phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x)‖^p) μ)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        ((n x^r) • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
          value phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x)‖^p ∂μ)^(1/p) ≤ C) :
    let central := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      value phaseIndex a level cell (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    Integrable (fun x => ‖(n x^r) • central x‖^p) μ ∧
      (∫ x, ‖(n x^r) • central x‖^p ∂μ)^(1/p) ≤ C := by
  let V := fun x s => ((n x^r:ℝ):ℂ) • value x s
  have hV : ∀ s, Measurable (fun x => V x s) :=
    fun s => ((hn.pow_const r).complex_ofReal).smul (hv s)
  have heq (z : ι → ℂ) (x : X) :
      g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop V
        phaseIndex a level cell z x = (n x^r) •
      g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
        phaseIndex a level cell z x :=
    g.sourceShiftFamily_real_weight tops slope precision cutoff weight K gap packets assigned stop
      value phaseIndex a level cell (fun x => n x^r) z x
  have hi : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop V
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ := by
    intro i eta
    simpa only [heq] using hvint i eta
  have hb : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop V
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C := by
    intro i eta
    simpa only [heq] using hvertex i eta
  have h := g.sourceShiftFamily_diagonal_lp μ tops slope precision cutoff weight hp hw hwmeas hK
    gap packets assigned stop V hV hassigned heligible phaseIndex a level cell
    (sourceShiftSimplex mu) (sourceShiftSimplex_convex mu) (mu^2) p C mu
    (fun _ h _ => h.1 _) (fun _ h => sourceShiftSimplex_sq_sum mu _ h) hp1 hC
    (sourceShiftSimplex_vertex hmu) hi hb
  simpa only [heq] using h

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLpDamping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant scalar damping acts exactly on the Lp root. The vertex
estimate on the prescribed imaginary ball therefore extends to the whole
tube using the manuscript's Gaussian tail estimate. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem source_lp_root_smul (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
    (c : ℂ) (p : ℝ) (hp : 0 < p) :
    (∫ x, ‖c • F x‖^p ∂μ)^(1/p) = ‖c‖*(∫ x, ‖F x‖^p ∂μ)^(1/p) := by
  have heq : (∫ x, ‖c • F x‖^p ∂μ) = ‖c‖^p*(∫ x, ‖F x‖^p ∂μ) := by
    simp_rw [norm_smul,Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
    exact integral_const_mul _ _
  rw [heq,Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg c),mul_one_div_cancel hp.ne',Real.rpow_one]

theorem source_lp_power_smul_integrable (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
    (c : ℂ) (p : ℝ) (hF : Integrable (fun x => ‖F x‖^p) μ) :
    Integrable (fun x => ‖c • F x‖^p) μ := by
  simp_rw [norm_smul,Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
  exact hF.const_mul _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceUniformDamping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian threshold is uniform in the finite number of phases.
This permits the manuscript choice K=blockCount(L) without fixing K
before choosing the lower threshold for L. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem eventually_damped_vertex_bound_finite (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (a eta : Fin n → ℝ) (mu P : ℝ) (value : ℂ),
      (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → 0 ≤ mu → mu ≤ 1 → 0 ≤ P →
      ‖value‖ ≤ P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp (C*Real.sqrt L) →
      (Real.sqrt (∑ i, (eta i)^2) ≤ L^2 → ‖value‖ ≤ P) →
      ‖gaussianPhaseDamping (phaseTubePoint a eta)*value‖ ≤ Real.exp 1*P := by
  filter_upwards [eventually_gaussian_imaginary_tail C hC] with L htail
  intro n a eta mu P value ha hsum hmu hmu1 hP hcrude hsmall
  let r := Real.sqrt (∑ i, (eta i)^2)
  have hr2 : r^2 = ∑ i, (eta i)^2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hd := gaussianPhaseDamping_simplex_le a eta mu ha hsum
  rw [← hr2] at hd
  rw [norm_mul]
  by_cases hr : r ≤ L^2
  · have hd1 : ‖gaussianPhaseDamping (phaseTubePoint a eta)‖ ≤ Real.exp 1 := by
      apply hd.trans (Real.exp_le_exp.mpr _)
      nlinarith [sq_nonneg r]
    exact mul_le_mul hd1 (hsmall hr) (norm_nonneg _) (Real.exp_pos _).le
  · have hlarge := htail mu r hmu hmu1 (le_of_not_ge hr)
    calc
      _ ≤ Real.exp (mu^2-r^2)*(P*(1+r)*Real.exp (C*Real.sqrt L)) :=
        mul_le_mul hd hcrude (norm_nonneg _) (Real.exp_pos _).le
      _ = P*((1+r)*Real.exp (mu^2-r^2+C*Real.sqrt L)) := by
        rw [Real.exp_add]
        ring
      _ ≤ P*1 := mul_le_mul_of_nonneg_left hlarge hP
      _ ≤ Real.exp 1*P := by
        have he : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
        nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVertexConstantBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Taking the manuscript exponent p=sqrt L absorbs the fixed polynomial
weight and stopping costs in the integrated vertex estimate. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_vertex_constant_budget (q A B K : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ α : ℝ, 1 ≤ α → α ≤ 3 →
      let cost := 1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1)
      (cost*(1+K*L^B*cost))^(1/Real.sqrt L) ≤ L^(2*q+1) := by
  filter_upwards [eventually_ge_atTop (max 1 (64*(1+K))),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (4*A+B+1)] with L hLbig hp
  intro α hα hα3
  dsimp only
  have hL : 1 ≤ L := (le_max_left _ _).trans hLbig
  have hLc : 64*(1+K) ≤ L := (le_max_right _ _).trans hLbig
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  let X := (L^q)^(Real.sqrt L)
  let Y := L^A
  let cost := 1+X*(Y+1)^(α-1)
  have hX : 1 ≤ X := Real.one_le_rpow (Real.one_le_rpow hL hq) hp0.le
  have hY : 1 ≤ Y := Real.one_le_rpow hL hA
  have hLB : 1 ≤ L^B := Real.one_le_rpow hL hB
  have hY2 : 1 ≤ Y^2 := one_le_pow₀ hY
  have hpow : (Y+1)^(α-1) ≤ 4*Y^2 := by
    calc
      _ ≤ (Y+1)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (Y+1)^2 := Real.rpow_two _
      _ ≤ 4*Y^2 := by nlinarith
  have hXY : 1 ≤ X*Y^2 := one_le_mul_of_one_le_of_one_le hX hY2
  have hcost : cost ≤ 8*X*Y^2 := by
    have h := mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hX)
    dsimp only [cost]
    nlinarith
  have hcost0 : 0 ≤ cost := by dsimp [cost]; positivity
  have hnext : 1+K*L^B*cost ≤ (1+K)*L^B*(8*X*Y^2) := by
    have hb : 1 ≤ L^B*(8*X*Y^2) :=
      one_le_mul_of_one_le_of_one_le hLB (by nlinarith)
    have hk := mul_le_mul_of_nonneg_left hcost (show 0 ≤ K*L^B by positivity)
    nlinarith
  have htotal : cost*(1+K*L^B*cost) ≤
      64*(1+K)*L^B*X^2*Y^4 := by
    have h := mul_le_mul hcost hnext (by positivity : 0 ≤ 1+K*L^B*cost)
      (by positivity : 0 ≤ 8*X*Y^2)
    nlinarith
  have hpower : L^B*X^2*Y^4 = L^(2*q*Real.sqrt L+4*A+B) := by
    dsimp only [X,Y]
    rw [← Real.rpow_natCast,← Real.rpow_mul (Real.rpow_nonneg hL0.le _),
      ← Real.rpow_mul hL0.le,← Real.rpow_natCast,← Real.rpow_mul hL0.le,
      ← Real.rpow_add hL0,← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  have hbase : cost*(1+K*L^B*cost) ≤ L^((2*q+1)*Real.sqrt L) := by
    calc
      _ ≤ 64*(1+K)*(L^B*X^2*Y^4) := by nlinarith [htotal]
      _ ≤ L*(L^B*X^2*Y^4) := mul_le_mul_of_nonneg_right hLc (by positivity)
      _ = L^(2*q*Real.sqrt L+4*A+B+1) := by
        rw [hpower]
        calc
          _ = L^(2*q*Real.sqrt L+4*A+B)*L^(1:ℝ) := by rw [Real.rpow_one]; ring
          _ = _ := (Real.rpow_add hL0 _ _).symm
      _ ≤ L^((2*q+1)*Real.sqrt L) :=
        Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ cost*(1+K*L^B*cost)) hbase
    (one_div_nonneg.mpr hp0.le)
  have heq : (L^((2*q+1)*Real.sqrt L))^(1/Real.sqrt L) = L^(2*q+1) := by
    rw [← Real.rpow_mul hL0.le]
    congr 1
    field_simp
  exact h.trans_eq heq

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTypeUniformMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical thresholds are chosen before all spatial and coefficient
index types. These are the existing source estimates with their universal
type binders moved inside the eventual statement; no bound changes. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
theorem eventually_source_crude_mass_budget_types (q b : ℝ) (_hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ (X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (μ : Measure X)
      (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (U S alpha r : ℝ),
      (∀ x, 0 < n x) → (∀ᵐ x ∂μ, n x ≤ U) → Measurable n → Integrable n μ →
      Measurable A → 0 < U → 0 ≤ S → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ r →
      Real.log U ≤ 3*L → (∫ x, n x ∂μ) ≤ L^b*S →
      (∀ᵐ x ∂μ, ‖A x‖ ≤ L^q*(1+r)*n x) →
      Integrable (fun x => ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L)) μ ∧
      (∫ x, ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L) ∂μ)^(1/Real.sqrt L) ≤
        (L^(q+1)*S^(1/Real.sqrt L))*(1+r)*Real.exp (6*Real.sqrt L) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop b] with L hL hpB
  intro X κ _ _ μ n A U S alpha r hn hnU hnmeas hnint hAmeas hU hS ha ha3 hr hlog hmass hnode
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  obtain ⟨hi,hbound⟩ := source_node_normalized_moment_ae μ n A U (L^q*(1+r))
    alpha (Real.sqrt L) hn hnU hnmeas hnint hAmeas hU (by positivity) ha hp hnode
  have hUpow : U^((alpha-1)/Real.sqrt L) ≤ Real.exp (6*Real.sqrt L) :=
    by
      have hs2 := Real.sq_sqrt hL0.le
      have he : 0 ≤ (alpha-1)/Real.sqrt L := div_nonneg (by linarith) hp.le
      rw [Real.rpow_def_of_pos hU]
      apply Real.exp_le_exp.mpr
      calc
        Real.log U*((alpha-1)/Real.sqrt L) ≤ (3*L)*((alpha-1)/Real.sqrt L) :=
          mul_le_mul_of_nonneg_right hlog he
        _ ≤ (3*L)*(2/Real.sqrt L) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith) hp.le) (by positivity)
        _ = 6*Real.sqrt L := by
          field_simp
          nlinarith
  have hmasspow : (∫ x, n x ∂μ)^(1/Real.sqrt L) ≤ L*S^(1/Real.sqrt L) := by
    have h := Real.rpow_le_rpow (integral_nonneg fun x => (hn x).le) hmass
      (one_div_nonneg.mpr hp.le)
    rw [Real.mul_rpow (Real.rpow_nonneg hL0.le _) hS,← Real.rpow_mul hL0.le] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hS _)
    calc
      L^(b*(1/Real.sqrt L)) ≤ L^((1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL (by
          have hbp := (div_le_one hp).mpr hpB
          simpa only [div_eq_mul_inv,one_div,one_mul] using hbp)
      _ = L := Real.rpow_one L
  refine ⟨hi,hbound.trans ?_⟩
  calc
    _ ≤ (L^q*(1+r))*Real.exp (6*Real.sqrt L)*(L*S^(1/Real.sqrt L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hUpow (by positivity)) hmasspow
        (Real.rpow_nonneg (integral_nonneg fun x => (hn x).le) _) (by positivity)
    _ = _ := by
      rw [show L^(q+1) = L^q*L from by rw [Real.rpow_add hL0,Real.rpow_one]]
      ring

theorem eventually_source_damped_vertex_root_types (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (n : ℕ) (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
      (a eta : Fin n → ℝ) (mu P p : ℝ),
      (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → 0 ≤ mu → mu ≤ 1 → 0 ≤ P → 0 < p →
      (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤
        P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp (C*Real.sqrt L) →
      (Real.sqrt (∑ i, (eta i)^2) ≤ L^2 → (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ P) →
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint a eta) • F x‖^p ∂μ)^(1/p) ≤
        Real.exp 1*P := by
  filter_upwards [eventually_damped_vertex_bound_finite C hC] with L hL
  intro X κ _ _ n μ F a eta mu P p ha hsum hmu hmu1 hP hp hcrude hsmall
  let V := (∫ x, ‖F x‖^p ∂μ)^(1/p)
  have hV : 0 ≤ V := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hnorm : ‖(V:ℂ)‖ = V := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hV]
  have h := hL n a eta mu P (V:ℂ) ha hsum hmu hmu1 hP
    (by simpa only [hnorm] using hcrude) (by simpa only [hnorm] using hsmall)
  rw [norm_mul,hnorm] at h
  rwa [source_lp_root_smul μ F _ p hp]

namespace AngularGrid
attribute [local instance] Classical.propDecidable
theorem eventually_source_tree_vertex_moment_types (q A B Pconst : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (μ : Measure X)
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
      (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
    ∀ (phase : ℕ → ℂ) (a alpha : ℝ), 1 ≤ alpha → alpha ≤ 3 →
    ∀ (Kb : ℕ), 0 < Kb → ∀ (shift : Fin Kb) (count : ℕ) (cell : ℤ)
      (good : Set X), MeasurableSet good → ∀ (bad : τ → Set X),
      (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty →
      (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
        ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count)) →
    let p := Real.sqrt L
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ x ∈ good, ∀ j ≤ count, ∀ c,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) c‖ ≤
        L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) c x) →
    (∀ x ∈ good, cost*
      (∑ t ∈ (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).filter
        (fun t => x ∈ bad t), weight t x) ≤ 1/2) →
    (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      Integrable ((good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a alpha p (L^A) shift t count x)) μ) →
    (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      (∫ x, (good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a alpha p (L^A) shift t count x) x ∂μ) ≤
        Pconst*L^B*cost*(∫ x, weight t x ∂μ)) →
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell
    let amp := fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell
    IntegrableOn (fun x => ‖(n x^(alpha/p-1)) • amp x‖^p) good μ ∧
      (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
        L^(2*q+1)*(∑ t ∈ g.cellTops tops slope precision cutoff
          (ShiftedBlocks.endpoint shift 0) cell, ∫ x, weight t x ∂μ)^(1/p) := by
  filter_upwards [eventually_source_vertex_constant_budget q A B (2*Pconst)
    hq hA hB (by positivity),eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro τ σ X κ _ _ μ g tops slope precision cutoff weight hp hw hwint hwmeas K gap packets assigned stop
    value hv phase a alpha ha ha3 Kb hKb shift count cell good hgood bad hne hterminal
    p cost henvelope hbad hpathInt hpathBound n amp
  have hp0 : 0 < p := Real.sqrt_pos.mpr (zero_lt_one.trans_le hL)
  have hM : 1 ≤ L^A := Real.one_le_rpow hL hA
  have hC : 0 ≤ L^q := Real.rpow_nonneg (zero_le_one.trans hL) _
  obtain ⟨hi,hbound⟩ := g.source_packet_vertex_moment μ tops slope precision cutoff weight hp hw
    hwint hwmeas K gap packets assigned stop value hv phase a alpha p hKb shift count cell
    (L^A) (L^q) (Pconst*L^B*cost) hM hC ha hp0 good hgood bad hne hterminal
    henvelope hbad hpathInt hpathBound
  let S := ∑ t ∈ g.cellTops tops slope precision cutoff
    (ShiftedBlocks.endpoint shift 0) cell, ∫ x, weight t x ∂μ
  have hS : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have heq : cost*(1+2*(Pconst*L^B*cost)) = cost*(1+(2*Pconst)*L^B*cost) := by ring
  have hbudget' : (cost*(1+(2*Pconst)*L^B*cost))^(1/p) ≤ L^(2*q+1) :=
    hbudget alpha ha ha3
  refine ⟨hi,?_⟩
  change (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤ L^(2*q+1)*S^(1/p)
  change (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
    (cost*(1+2*(Pconst*L^B*cost))*S)^(1/p) at hbound
  rw [heq,Real.mul_rpow (mul_nonneg hcost (by positivity)) hS] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hbudget' (Real.rpow_nonneg hS _))

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceTypeUniformInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical thresholds are chosen before all spatial and coefficient
index types. These are the existing source estimates with their universal
type binders moved inside the eventual statement; no bound changes. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
namespace AngularGrid
attribute [local instance] Classical.propDecidable
theorem eventually_source_diagonal_finite_phases_types
    (q b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (nphases : ℕ), 0 < nphases →
    ∀ (μ : Measure X) [IsFiniteMeasure μ]
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ), 0 < K → ∀ (gap : ℕ → ℝ)
      (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (phaseIndex : ℕ → (Fin nphases)) (a : ℝ) (level : ℕ) (cell : ℤ)
      (n : X → ℝ) (U S alpha mu : ℝ),
      Measurable n → Integrable n μ → (∀ x, 0 < n x) → (∀ᵐ x ∂μ, n x ≤ U) →
      0 < U → 0 ≤ S → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ mu → mu ≤ 1 →
      Real.log U ≤ 3*L → (∫ x, n x ∂μ) ≤ L^b*S →
    let p := Real.sqrt L
    let F := g.sourceShiftFamily tops slope precision cutoff weight K gap
      packets assigned stop value phaseIndex a level cell
    (∀ i : (Fin nphases), ∀ eta, ∀ᵐ x ∂μ, ‖F (phaseTubePoint (Pi.single i mu) eta) x‖ ≤
      L^q*(1+Real.sqrt (∑ j, (eta j)^2))*n x) →
    (∀ i : (Fin nphases), ∀ eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤
        L^(q+1)*S^(1/p)) →
    let central := F (phaseTubePoint (fun _ => mu/(Fintype.card (Fin nphases):ℝ)) (fun _ => 0))
    Integrable (fun x => ‖(n x^(alpha/p-1)) • central x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • central x‖^p ∂μ)^(1/p) ≤ L^(q+2)*S^(1/p) := by
  filter_upwards [eventually_source_crude_mass_budget_types q b hb,
    eventually_source_damped_vertex_root_types 6 (by norm_num),
    eventually_ge_atTop (max 1 (Real.exp 1))] with L hcrude hdamp hLbig
  intro τ σ X κ _ _ nphases hnphases μ _ g tops slope precision cutoff weight hp hw hwmeas K hK gap packets assigned stop
    value hv hassigned heligible phaseIndex a level cell n U S alpha mu hn hnint hnpos hnU
    hU hS ha ha3 hmu hmu1 hlog hmass p F hnode hsmall central
  let : Nonempty (Fin nphases) := ⟨⟨0,hnphases⟩⟩
  have hL : 1 ≤ L := (le_max_left _ _).trans hLbig
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < p := Real.sqrt_pos.mpr hL0
  have hP : 0 ≤ L^(q+1)*S^(1/p) := by positivity
  have hraw (i : (Fin nphases)) (eta : (Fin nphases) → ℝ) :
      Integrable (fun x => ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤
        (L^(q+1)*S^(1/p))*(1+Real.sqrt (∑ j, (eta j)^2))*Real.exp (6*Real.sqrt L) := by
    apply hcrude X κ μ n (F (phaseTubePoint (Pi.single i mu) eta)) U S alpha
      (Real.sqrt (∑ j, (eta j)^2)) hnpos hnU hn hnint
    · exact g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas
        K gap packets assigned stop value hv _ a level cell
    · exact hU
    · exact hS
    · exact ha
    · exact ha3
    · exact Real.sqrt_nonneg _
    · exact hlog
    · exact hmass
    · exact hnode i eta
  have hvertices (i : (Fin nphases)) (eta : (Fin nphases) → ℝ) :
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        ((n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x)‖^p ∂μ)^(1/p) ≤
          L^(q+2)*S^(1/p) := by
    have hsimplex := sourceShiftSimplex_vertex (ι := Fin nphases) hmu i
    have hd := hdamp X κ nphases μ (fun x => (n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x)
      (Pi.single i mu) eta mu (L^(q+1)*S^(1/p)) p
      hsimplex.1 hsimplex.2 hmu hmu1 hP hp0 (hraw i eta).2 (hsmall i eta)
    apply hd.trans
    calc
      Real.exp 1*(L^(q+1)*S^(1/p)) ≤ L*(L^(q+1)*S^(1/p)) :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hLbig) hP
      _ = L^(q+2)*S^(1/p) := by
        have he : L*L^(q+1) = L^(q+2) := by
          calc
            L*L^(q+1) = L^(1:ℝ)*L^(q+1) := by rw [Real.rpow_one]
            _ = L^(q+2) := by rw [← Real.rpow_add hL0]; congr 1; ring
        rw [← mul_assoc,he]
  exact g.sourceShiftFamily_normalized_diagonal_lp μ tops slope precision cutoff weight hp hw hwmeas
    hK gap packets assigned stop value hv hassigned heligible phaseIndex a level cell
    n hn (alpha/p-1) p (L^(q+2)*S^(1/p)) mu
    (by
      have hexp : 1 < Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
      have hLgt : 1 < L := hexp.trans_le ((le_max_right _ _).trans hLbig)
      exact (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)).mpr (by simpa using hLgt))
    (by positivity) hmu
    (fun i eta => source_lp_power_smul_integrable μ _ _ p (hraw i eta).1) hvertices

theorem eventually_source_root_diagonal_from_paths_types (q A B Pconst : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (μ : Measure X)
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ) (hK : 0 < K), ∀ (gap : ℕ → ℝ) (packets : Finset σ)
      (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (root : ℤ) (good : Set X), MeasurableSet good →
    ∀ [IsFiniteMeasure (μ.restrict good)] (U a alpha mu : ℝ),
      0 < U → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ mu → mu ≤ 1 → Real.log U ≤ 3*L →
      (g.cellTops tops slope precision cutoff 0 root).Nonempty →
    let p := Real.sqrt L
    let n := g.mass tops slope precision cutoff weight 0 root
    let F := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      value (ShiftedBlocks.tag hK) a 0 root
    let phase := fun (i : Fin K) (eta : Fin K → ℝ) (j : ℕ) =>
      phaseTubePoint (Pi.single i mu) eta (ShiftedBlocks.tag hK j)
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ x ∈ good, n x ≤ U) →
    (∀ (i : Fin K) eta x, x ∈ good →
      ‖F (phaseTubePoint (Pi.single i mu) eta) x‖ ≤
        L^(2*q)*(1+Real.sqrt (∑ j, (eta j)^2))*n x) →
    ∀ (count : Fin K → ℕ) (bad : Fin K → (Fin K → ℝ) → τ → Set X),
      (∀ i, ∀ t ∈ g.cellTops tops slope precision cutoff 0 root,
        ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint i (count i))) →
    (∀ i eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∀ x ∈ good, ∀ j ≤ count i, ∀ c,
        ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (phase i eta) a x (ShiftedBlocks.endpoint i j) c‖ ≤
          L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint i j) c x) ∧
      (∀ x ∈ good, cost*
        (∑ t ∈ (g.cellTops tops slope precision cutoff 0 root).filter
          (fun t => x ∈ bad i eta t), weight t x) ≤ 1/2) ∧
      (∀ t ∈ g.cellTops tops slope precision cutoff 0 root,
        Integrable ((good\bad i eta t).indicator (fun x => weight t x*
          g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
            (phase i eta) a alpha p (L^A) i t (count i) x)) μ) ∧
      (∀ t ∈ g.cellTops tops slope precision cutoff 0 root,
        (∫ x, (good\bad i eta t).indicator (fun x => weight t x*
          g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
            (phase i eta) a alpha p (L^A) i t (count i) x) x ∂μ) ≤
          Pconst*L^B*cost*(∫ x, weight t x ∂μ))) →
    let central := F (phaseTubePoint (fun _ => mu/(K:ℝ)) (fun _ => 0))
    let S := ∑ t ∈ tops, ∫ x, weight t x ∂μ
    IntegrableOn (fun x => ‖(n x^(alpha/p-1)) • central x‖^p) good μ ∧
      (∫ x in good, ‖(n x^(alpha/p-1)) • central x‖^p ∂μ)^(1/p) ≤
        L^(2*q+2)*S^(1/p) := by
  filter_upwards [eventually_source_tree_vertex_moment_types
      q A B Pconst hq hA hB hP,
    eventually_source_diagonal_finite_phases_types (2*q) 0 (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L htree hinterp hL
  intro τ σ X κ _ _ μ g tops slope precision cutoff weight hp hw hwint hwmeas K hK gap packets
    assigned stop value hv hassigned heligible root good hgood _ U a alpha mu
    hU ha ha3 hmu hmu1 hlog hne p n F phase cost hnU hnode count bad hterminal hpaths central S
  have hp0 : 0 < p := Real.sqrt_pos.mpr (zero_lt_one.trans_le hL)
  let roots := g.cellTops tops slope precision cutoff 0 root
  have hrtop {t : τ} (ht : t ∈ roots) : t ∈ tops :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1
  have hSn : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le
  have hrootS : (∑ t ∈ roots, ∫ x, weight t x ∂μ) ≤ S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      exact hrtop ht
    · intro t _ _
      exact integral_nonneg fun x => (hw t x).le
  have hnint : Integrable n μ := integrable_finsetSum roots (fun t ht => hwint t (hrtop ht))
  have hnpos : ∀ x, 0 < n x := by
    obtain ⟨t,ht⟩ := hne
    exact fun x => g.mass_pos_of_member tops slope precision cutoff weight hw 0 root x ht
  have hmass : (∫ x, n x ∂μ.restrict good) ≤ L^(0:ℝ)*S := by
    rw [Real.rpow_zero,one_mul]
    apply (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => (hnpos x).le) hnint).trans
    rw [show (∫ x, n x ∂μ) = ∑ t ∈ roots, ∫ x, weight t x ∂μ from
      integral_finsetSum roots (fun t ht => hwint t (hrtop ht))]
    exact hrootS
  have hsmall (i : Fin K) (eta : Fin K → ℝ) (heta : Real.sqrt (∑ j, (eta j)^2) ≤ L^2) :
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p
        ∂μ.restrict good)^(1/p) ≤ L^(2*q+1)*S^(1/p) := by
    obtain ⟨henv,hbad,hpi,hpb⟩ := hpaths i eta heta
    have ht := htree τ σ X κ μ g tops slope precision cutoff weight hp hw hwint hwmeas K gap packets
      assigned stop value hv (phase i eta) a alpha ha ha3 K hK i (count i) root good hgood
      (bad i eta) (by simpa only [ShiftedBlocks.endpoint_zero] using hne)
      (by simpa only [ShiftedBlocks.endpoint_zero] using hterminal i) henv
      (by simpa only [ShiftedBlocks.endpoint_zero] using hbad)
      (by simpa only [ShiftedBlocks.endpoint_zero] using hpi)
      (by simpa only [ShiftedBlocks.endpoint_zero] using hpb)
    have hb' : (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p
        ∂μ.restrict good)^(1/p) ≤ L^(2*q+1)*
          (∑ t ∈ roots, ∫ x, weight t x ∂μ)^(1/p) := by
      simpa only [p,n,F,phase,roots,sourceShiftFamily,ShiftedBlocks.endpoint_zero] using ht.2
    apply hb'.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le)
        hrootS (one_div_nonneg.mpr hp0.le)) (by positivity)
  have hi := hinterp τ σ X κ K hK (μ.restrict good) g tops slope precision cutoff weight hp hw hwmeas
    K hK gap packets assigned stop value hv hassigned heligible (ShiftedBlocks.tag hK)
    a 0 root n U S alpha mu (g.measurable_mass tops slope precision cutoff weight hwmeas 0 root)
    hnint.restrict hnpos (by
      filter_upwards [ae_restrict_mem hgood] with x hx
      exact hnU x hx) hU hSn ha ha3 hmu hmu1 hlog hmass
    (by
      intro i eta
      filter_upwards [ae_restrict_mem hgood] with x hx
      exact hnode i eta x hx) hsmall
  simpa only [p,central,F,Fintype.card_fin,IntegrableOn] using hi

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCentralPowerGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical gain in manuscript §11, with the actual rounded number
of shifts. A polynomial separated-count bound gives the required phase
lower bound, and the central exponent absorbs every fixed power of L. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

 theorem eventually_phaseParameter_lower (d : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
      (phaseConstant/(d+1))/Real.log L ≤ phaseParameter D := by
  filter_upwards [eventually_ge_atTop (2:ℝ)] with L hL
  intro D hD hDupper
  have hL0 : 0 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogD : 0 < Real.log (2*D) := Real.log_pos (by linarith)
  have hden : Real.log (2*D) ≤ (d+1)*Real.log L := by
    calc
      _ = Real.log 2+Real.log D := Real.log_mul (by norm_num) (by linarith)
      _ ≤ Real.log L+Real.log (L^d) := add_le_add
        (Real.log_le_log (by norm_num) hL)
        (Real.log_le_log (by linarith) hDupper)
      _ = (d+1)*Real.log L := by rw [Real.log_rpow hL0]; ring
  have h := div_le_div_of_nonneg_left phaseConstant_pos.le hlogD hden
  change _ ≤ phaseConstant/Real.log (2*D)
  calc
    _ = phaseConstant/((d+1)*Real.log L) := by rw [div_div]
    _ ≤ _ := h

 theorem central_exponent_gap {L c alpha K : ℝ}
    (hL : 1 < L) (hc : 0 < c) (hlog : 4/c ≤ Real.log L)
    (halpha : c/Real.log L ≤ alpha-2) (halpha3 : alpha ≤ 3)
    (hK : Real.log L^2 ≤ K) :
    c/(2*Real.sqrt L*Real.log L) ≤
      (alpha-2-(alpha-1)/K)/Real.sqrt L := by
  have ht : 0 < Real.log L := Real.log_pos hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hK0 : 0 < K := (sq_pos_of_pos ht).trans_le hK
  have hsmall : 2/K ≤ c/(2*Real.log L) := by
    calc
      _ ≤ 2/(Real.log L^2) :=
        div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ht) hK
      _ ≤ c/(2*Real.log L) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos ht) (by positivity)).mpr
        have hcLog : 4 ≤ c*Real.log L := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hlog
        nlinarith [mul_le_mul_of_nonneg_right hcLog ht.le]
  have hterm : (alpha-1)/K ≤ 2/K :=
    div_le_div_of_nonneg_right (by linarith) hK0.le
  have hgap : c/(2*Real.log L) ≤ alpha-2-(alpha-1)/K := by
    have heq : c/Real.log L = 2*(c/(2*Real.log L)) := by ring
    linarith
  calc
    _ = (c/(2*Real.log L))/Real.sqrt L := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hgap hs.le

 theorem eventually_source_central_power_gain (c C Q : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ alpha K N : ℝ,
      c/Real.log L ≤ alpha-2 → alpha ≤ 3 →
      Real.log L^2 ≤ K → 0 < N → L/2 ≤ Real.log N →
      L^C*N^(1+(2-alpha)/Real.sqrt L+((alpha-1)/Real.sqrt L)/K) ≤ L^(-Q)*N := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (by norm_num : (0:ℝ) < 1/2)).bound
      (show 0 < c/(4*(C+Q+1)) by positivity)
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4/c),hsmall]
    with L hL hlog hsmallL
  intro alpha K N halpha halpha3 hK hN hmass
  have hL0 : 0 < L := by linarith
  have ht : 0 < Real.log L := Real.log_pos hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hK0 : 0 < K := (sq_pos_of_pos ht).trans_le hK
  rw [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0.le _),
    ← Real.sqrt_eq_rpow] at hsmallL
  let delta := (alpha-2-(alpha-1)/K)/Real.sqrt L
  have hdelta : c/(2*Real.sqrt L*Real.log L) ≤ delta :=
    central_exponent_gap hL hc hlog halpha halpha3 hK
  have hdelta0 : 0 ≤ delta := (by positivity : 0 ≤ c/(2*Real.sqrt L*Real.log L)).trans hdelta
  have hproduct : c*Real.sqrt L/(4*Real.log L) ≤ delta*Real.log N := by
    calc
      _ = (c/(2*Real.sqrt L*Real.log L))*(L/2) := by
        field_simp
        nlinarith [Real.sq_sqrt hL0.le]
      _ ≤ delta*Real.log N := mul_le_mul hdelta hmass (by positivity) hdelta0
  have hcost : (C+Q)*Real.log L ≤ c*Real.sqrt L/(4*Real.log L) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.log L)).mpr
    have hb := (le_div_iff₀ (show 0 < 4*(C+Q+1) by positivity)).mp
      (show (Real.log L)^2 ≤ (c*Real.sqrt L)/(4*(C+Q+1)) by
        simpa only [div_mul_eq_mul_div] using hsmallL)
    nlinarith [sq_nonneg (Real.log L)]
  have hexponent : 1+(2-alpha)/Real.sqrt L+((alpha-1)/Real.sqrt L)/K = 1-delta := by
    dsimp only [delta]
    field_simp
    ring
  rw [hexponent,Real.rpow_def_of_pos hL0,Real.rpow_def_of_pos hN,
    ← Real.exp_add,Real.rpow_def_of_pos hL0,← Real.exp_log hN,← Real.exp_add]
  rw [Real.log_exp]
  apply Real.exp_le_exp.mpr
  nlinarith [hcost.trans hproduct]

/-- The manuscript's rounded shift count satisfies the numerical hypothesis
without replacing it by an unrounded real parameter. -/
theorem eventually_source_central_power_gain_actual (d C Q : ℝ)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → D ≤ L^d → 0 < N → L/2 ≤ Real.log N →
      L^C*N^(1-phaseParameter D/Real.sqrt L+
        ((1+phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ)) ≤
        L^(-Q)*N := by
  have hc : 0 < phaseConstant/(d+1) := div_pos phaseConstant_pos (by linarith)
  filter_upwards [eventually_phaseParameter_lower d,
    eventually_source_central_power_gain (phaseConstant/(d+1)) C Q hc hC hQ]
    with L hphase hgain
  intro D N hD hDbound hN hmass
  have hrange := phaseParameter_range hD
  have h := hgain (2+phaseParameter D) (SourceParameters.blockCount L:ℝ) N
    (by simpa only [add_sub_cancel_left] using hphase D hD hDbound)
    (by change 2+phaseConstant/Real.log (2*D) ≤ 3; linarith)
    (Nat.le_ceil _) hN hmass
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCentralBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mass and measure bounds in §11 give the precise power of N in
the central estimate. The previously proved exponent gain then absorbs
all of the fixed polynomial factors. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

 theorem central_root_budget {L N F S q p gamma : ℝ}
    (hL : 1 ≤ L) (hN : 0 < N) (hF : 0 < F) (hS : 0 ≤ S)
    (hq : 0 ≤ q) (hp : 1 ≤ p) (hgamma2 : gamma ≤ 2)
    (hSupper : S ≤ L^q*N^2*F) :
    (L^q*S^(1/p))*F^(1-1/p)*(L^q*N)^gamma ≤
      L^(4*q)*F*N^(gamma+2/p) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpinv : 1/p ≤ 1 := (div_le_one hp0).mpr hp
  have hSpow := Real.rpow_le_rpow hS hSupper (one_div_nonneg.mpr hp0.le)
  have hSprod : (L^q*N^2*F)^(1/p) = L^(q/p)*N^(2/p)*F^(1/p) := by
    rw [Real.mul_rpow (by positivity) hF.le,
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hL0.le,← Real.rpow_natCast,← Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    simp only [div_eq_mul_inv,one_mul]
  have hFprod : F^(1/p)*F^(1-1/p) = F := by
    rw [← Real.rpow_add hF]
    rw [show 1/p+(1-1/p) = (1:ℝ) by ring,Real.rpow_one]
  have hLprod : L^q*L^(q/p)*(L^q)^gamma = L^(q+q/p+q*gamma) := by
    rw [← Real.rpow_mul hL0.le,← Real.rpow_add hL0,← Real.rpow_add hL0]
  have hNprod : N^(2/p)*N^gamma = N^(gamma+2/p) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ (L^q*(L^q*N^2*F)^(1/p))*F^(1-1/p)*(L^q*N)^gamma := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSpow (by positivity))
          (by positivity)) (by positivity)
    _ = L^(q+q/p+q*gamma)*F*N^(gamma+2/p) := by
      rw [hSprod,Real.mul_rpow (by positivity) hN.le]
      calc
        _ = (L^q*L^(q/p)*(L^q)^gamma)*(F^(1/p)*F^(1-1/p))*(N^(2/p)*N^gamma) := by ring
        _ = _ := by rw [hLprod,hFprod,hNprod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hF.le
      apply Real.rpow_le_rpow_of_exponent_le hL
      have hqp : q/p ≤ q := by
        have h := mul_le_mul_of_nonneg_left hpinv hq
        simpa only [mul_one,mul_one_div] using h
      have hqgamma := mul_le_mul_of_nonneg_left hgamma2 hq
      nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCentralHolderAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The central Hölder estimate needs the mass cap only almost
 everywhere. In the application the measure is restricted to the
 constructed common good set. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem central_weight_integral_ae (μ : Measure X) [IsFiniteMeasure μ]
    (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (alpha p beta M B : ℝ)
    (hn : ∀ x, 0 < n x) (hnM : ∀ᵐ x ∂μ, n x ≤ M)
    (hnmeas : Measurable n) (hA : Measurable A) (hp : 1 < p) (hM : 0 ≤ M)
    (hgamma : 0 ≤ 1-alpha/p+beta)
    (henergy : Integrable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) μ)
    (hmoment : (∫ x, ‖(n x^(alpha/p-1)) • A x‖^p ∂μ)^(1/p) ≤ B) :
    Integrable (fun x => n x^beta*‖A x‖) μ ∧
      (∫ x, n x^beta*‖A x‖ ∂μ) ≤
        B*(μ.real Set.univ)^(1-1/p)*M^(1-alpha/p+beta) := by
  let F := fun x => (n x^(alpha/p-1)) • A x
  have hFmeas : Measurable F := (hnmeas.pow_const _).smul hA
  have hp0 : 0 < p := by linarith
  have hpzero : ENNReal.ofReal p ≠ 0 := by
    simpa only [ne_eq,ENNReal.ofReal_eq_zero,not_le] using hp0
  have hFp : MemLp F (ENNReal.ofReal p) μ :=
    (integrable_norm_rpow_iff hFmeas.aestronglyMeasurable hpzero (by simp)).mp
      (by simpa only [ENNReal.toReal_ofReal hp0.le] using henergy)
  have hFi : Integrable F μ := hFp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hpoint : ∀ᵐ x ∂μ, n x^beta*‖A x‖ ≤ M^(1-alpha/p+beta)*‖F x‖ := by
    filter_upwards [hnM] with x hx
    rw [central_weight_factorization (hn x)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hn x).le hx hgamma) (norm_nonneg _)
  have hleft : Integrable (fun x => n x^beta*‖A x‖) μ :=
    (hFi.norm.const_mul (M^(1-alpha/p+beta))).mono'
      ((hnmeas.pow_const _).mul hA.norm).aestronglyMeasurable
      (by
        filter_upwards [hpoint] with x hx
        rwa [Real.norm_eq_abs,abs_of_nonneg
          (mul_nonneg (Real.rpow_nonneg (hn x).le _) (norm_nonneg _))])
  have hpq : p.HolderConjugate (p/(p-1)) := Real.HolderConjugate.conjExponent hp
  have hq : 1/(p/(p-1)) = 1-1/p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => norm_nonneg (F x))
    (Filter.Eventually.of_forall fun _ : X => (zero_le_one : (0:ℝ) ≤ 1))
    hFp.norm (memLp_const (1:ℝ))
  simp only [mul_one,Real.one_rpow,integral_const,smul_eq_mul] at hh
  rw [hq] at hh
  have hnorm : (∫ x, ‖F x‖ ∂μ) ≤ B*(μ.real Set.univ)^(1-1/p) := by
    apply hh.trans
    exact mul_le_mul_of_nonneg_right hmoment (Real.rpow_nonneg (by positivity) _)
  refine ⟨hleft,?_⟩
  calc
    _ ≤ ∫ x, M^(1-alpha/p+beta)*‖F x‖ ∂μ :=
      integral_mono_ae hleft (hFi.norm.const_mul _) hpoint
    _ = M^(1-alpha/p+beta)*(∫ x, ‖F x‖ ∂μ) := integral_const_mul _ _
    _ ≤ M^(1-alpha/p+beta)*(B*(μ.real Set.univ)^(1-1/p)) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hM _)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCentralBudgetAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source exponent budget under an almost-everywhere mass cap,
 as required on the common good set. The constants and exponents are
 identical to the pointwise version. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

 theorem source_central_estimate_ae {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (μ : Measure X) [IsFiniteMeasure μ] (n : X → ℝ) (amp : X → EuclideanSpace ℂ κ)
    (L N F S q p alpha beta : ℝ)
    (hL : 1 ≤ L) (hN : 0 < N) (hF : 0 < F) (hS : 0 ≤ S) (hq : 0 ≤ q)
    (hp : 1 < p) (hgamma : 0 ≤ 1-alpha/p+beta) (hgamma2 : 1-alpha/p+beta ≤ 2)
    (hn : ∀ x, 0 < n x) (hnM : ∀ᵐ x ∂μ, n x ≤ L^q*N)
    (hnmeas : Measurable n) (hamp : Measurable amp)
    (hmeasure : μ.real Set.univ ≤ F) (hSupper : S ≤ L^q*N^2*F)
    (henergy : Integrable (fun x => ‖(n x^(alpha/p-1)) • amp x‖^p) μ)
    (hmoment : (∫ x, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤ L^q*S^(1/p)) :
    Integrable (fun x => n x^beta*‖amp x‖) μ ∧
      (∫ x, n x^beta*‖amp x‖ ∂μ) ≤
        L^(4*q)*F*N^(1+(2-alpha)/p+beta) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < p := by linarith
  have hFpower : (μ.real Set.univ)^(1-1/p) ≤ F^(1-1/p) :=
    Real.rpow_le_rpow (by positivity) hmeasure
      (by have := (div_le_one hp0).mpr hp.le; linarith)
  obtain ⟨hi,hb⟩ := central_weight_integral_ae μ n amp alpha p beta (L^q*N) (L^q*S^(1/p))
    hn hnM hnmeas hamp hp (by positivity) hgamma henergy hmoment
  refine ⟨hi,?_⟩
  calc
    _ ≤ (L^q*S^(1/p))*(μ.real Set.univ)^(1-1/p)*(L^q*N)^(1-alpha/p+beta) := hb
    _ ≤ (L^q*S^(1/p))*F^(1-1/p)*(L^q*N)^(1-alpha/p+beta) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFpower (by positivity)) (by positivity)
    _ ≤ L^(4*q)*F*N^((1-alpha/p+beta)+2/p) :=
      central_root_budget hL hN hF hS hq hp.le hgamma2 hSupper
    _ = _ := by
      congr 2
      ring

/-- The actual source phase and shift count give the central negative-power
estimate once the normalized vertex moment has been established. -/
theorem eventually_source_central_integral_gain_ae (d q Q : ℝ)
    (hd : 0 ≤ d) (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (X κ : Type*) [MeasurableSpace X] [Fintype κ]
      (μ : Measure X) [IsFiniteMeasure μ] (n : X → ℝ) (amp : X → EuclideanSpace ℂ κ)
      (N F S : ℝ), 0 < N → 0 < F → 0 ≤ S → L/2 ≤ Real.log N →
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let beta := ((1+PhaseCombinatorics.phaseParameter D)/p)/(SourceParameters.blockCount L:ℝ)
    (∀ x, 0 < n x) → (∀ᵐ x ∂μ, n x ≤ L^q*N) → Measurable n → Measurable amp →
    μ.real Set.univ ≤ F → S ≤ L^q*N^2*F →
    Integrable (fun x => ‖(n x^(alpha/p-1)) • amp x‖^p) μ →
    (∫ x, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤ L^q*S^(1/p) →
    Integrable (fun x => n x^beta*‖amp x‖) μ ∧
      (∫ x, n x^beta*‖amp x‖ ∂μ) ≤ L^(-Q)*N*F := by
  filter_upwards [eventually_ge_atTop (16:ℝ),
    eventually_source_central_power_gain_actual d (4*q) Q hd (by positivity) hQ]
    with L hL hgain
  intro D hD hDb X κ _ _ μ _ n amp N F S hN hF hS hlog p alpha beta
    hn hnM hnmeas hamp hmeasure hSupper henergy hmoment
  have hp4 : 4 ≤ p := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith [hL])
  have hp0 : 0 < p := by linarith
  have htheta := PhaseCombinatorics.phaseParameter_range hD
  change 0 < PhaseCombinatorics.phaseParameter D ∧
    PhaseCombinatorics.phaseParameter D ≤ 1/3 at htheta
  obtain ⟨htheta0,htheta1⟩ := htheta
  have hK : (1:ℝ) ≤ SourceParameters.blockCount L := by
    exact_mod_cast SourceParameters.blockCount_pos (show 1 < L by linarith)
  have halpha : 0 ≤ alpha/p := div_nonneg (by dsimp [alpha]; linarith) hp0.le
  have halpha1 : alpha/p ≤ 1 := (div_le_one hp0).mpr (by dsimp [alpha]; linarith)
  have hbeta0 : 0 ≤ beta := by
    exact div_nonneg (div_nonneg (by linarith) hp0.le) (zero_le_one.trans hK)
  have hbeta1 : beta ≤ 1 := by
    apply (div_le_self (div_nonneg (by linarith) hp0.le) hK).trans
    exact (div_le_one hp0).mpr (by linarith)
  obtain ⟨hi,hb⟩ := source_central_estimate_ae μ n amp L N F S q p alpha beta
    (by linarith) hN hF hS hq (by linarith) (by linarith) (by linarith)
    hn hnM hnmeas hamp hmeasure hSupper henergy hmoment
  refine ⟨hi,?_⟩
  have hexp : 1+(2-alpha)/p+beta = 1-PhaseCombinatorics.phaseParameter D/Real.sqrt L+
      ((1+PhaseCombinatorics.phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ) := by
    dsimp only [alpha,beta,p]
    ring
  rw [hexp] at hb
  calc
    _ ≤ L^(4*q)*F*N^(1-PhaseCombinatorics.phaseParameter D/Real.sqrt L+
        ((1+PhaseCombinatorics.phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ)) := hb
    _ = (L^(4*q)*N^(1-PhaseCombinatorics.phaseParameter D/Real.sqrt L+
        ((1+PhaseCombinatorics.phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ)))*F := by ring
    _ ≤ (L^(-Q)*N)*F := mul_le_mul_of_nonneg_right (hgain D N hD hDb hN hlog) hF.le
    _ = _ := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePolynomialMassLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial mass cap in §11 fits in log U ≤ 3L when log N ≤ 2L. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_polynomial_mass_log (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L →
      Real.log (L^C*N) ≤ 3*L := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1)).bound
    (show 0 < 1/(|C|+1) by positivity)
  filter_upwards [hlog,eventually_ge_atTop (1:ℝ)] with L hlog hL
  intro N hN hlogN
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hlog0 := Real.log_nonneg hL
  rw [Real.rpow_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hlog0,
    abs_of_pos hL0] at hlog
  have hden : 0 < |C|+1 := by positivity
  have hb : (|C|+1)*Real.log L ≤ L := by
    calc
      _ ≤ (|C|+1)*(1/(|C|+1)*L) := mul_le_mul_of_nonneg_left hlog hden.le
      _ = L := by field_simp
  have hCL : C*Real.log L ≤ L :=
    (mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith)) hlog0).trans hb
  rw [Real.log_mul (Real.rpow_pos_of_pos hL0 C).ne' hN.ne',Real.log_rpow hL0]
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRootCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty eligible root cells of the actual translated grid.
They split the central packet sum exactly. A slope interval no wider
than one root contains at most two roots, including its endpoints. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mem_sourceRootCells (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (cell : ℤ) :
    cell ∈ g.sourceRootCells tops slope precision cutoff ↔
      (g.cellTops tops slope precision cutoff 0 cell).Nonempty := by
  constructor
  · rintro h
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
    exact ⟨t,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨ht,rfl,he⟩⟩
  · rintro ⟨t,ht⟩
    obtain ⟨ht,hindex,he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,he⟩,hindex⟩

theorem sourceRootCells_card_le_two (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff start : ℝ)
    (hslope : ∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) :
    (g.sourceRootCells tops slope precision cutoff).card ≤ 2 := by
  let left := ⌊(start-g.origin)/g.rootWidth⌋
  apply (Finset.card_le_card (t := {left,left+1}) ?_).trans Finset.card_le_two
  intro c hc
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc
  have ht' := (Finset.mem_filter.mp ht).1
  obtain ⟨hlo,hhi⟩ := hslope t ht'
  have hlo' : (start-g.origin)/g.rootWidth ≤ (slope t-g.origin)/g.rootWidth :=
    div_le_div_of_nonneg_right (by linarith) g.rootWidth_pos.le
  have hhi' : (slope t-g.origin)/g.rootWidth ≤ (start-g.origin)/g.rootWidth+1 := by
    apply (div_le_iff₀ g.rootWidth_pos).mpr
    rw [add_mul,div_mul_cancel₀ _ g.rootWidth_pos.ne',one_mul]
    linarith
  have h1 : left ≤ g.index 0 (slope t) := by
    simpa only [left,index,pow_zero,mul_one] using Int.floor_mono hlo'
  have h2 : g.index 0 (slope t) ≤ left+1 := by
    simpa only [left,index,pow_zero,mul_one,Int.floor_add_one] using Int.floor_mono hhi'
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

theorem sourceRootCells_packet_cover (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) :
    ∀ s ∈ packets, g.index 0 (slope (assigned s)) ∈
      g.sourceRootCells tops slope precision cutoff := by
  intro s hs
  apply Finset.mem_image.mpr
  refine ⟨assigned s,Finset.mem_filter.mpr ⟨hassigned s hs,?_⟩,rfl⟩
  exact g.eligible_of_le (hp _ (hassigned s hs)) (Nat.zero_le _) (heligible s hs)

/-- The globally weighted central packet sum is the sum of its actual
nonempty eligible roots; no packet is assigned to an artificial root. -/
theorem sourceBoundarySum_root_decomposition (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ) (value : σ → E)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (x : X) :
    (∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x : ℝ):ℂ) • value s) =
    ∑ c ∈ g.sourceRootCells tops slope precision cutoff,
      ((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          value (fun _ => (a:ℂ)) a x 0 c := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g.sourceRootCells_packet_cover tops slope precision cutoff hp packets assigned stop
      hassigned heligible)]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [g.sourcePacketAmplitude_equal_coordinates tops slope precision cutoff weight hp hw hK
    gap packets assigned stop value hassigned heligible a x c]
  congr 1
  ext s
  simp only [packetSet,Finset.mem_filter,Nat.zero_le,and_true]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRootIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root estimates integrate the exact boundary-weighted packet sum.
At most two nonempty eligible roots occur in the bounded slope range,
so this final spatial sum has only an absolute factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem sourceBoundarySum_integral_le (μ : Measure X)
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwmeas : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a start B : ℝ) (hB : 0 ≤ B)
    (hslope : ∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth)
    (hrootInt : ∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      Integrable (fun x => ‖((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (fun _ => (a:ℂ)) a x 0 c‖) μ)
    (hrootBound : ∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      (∫ x, ‖((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (fun _ => (a:ℂ)) a x 0 c‖ ∂μ) ≤ B) :
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x:ℝ):ℂ) • value x s
    Integrable (fun x => ‖W x‖) μ ∧ (∫ x, ‖W x‖ ∂μ) ≤ 2*B := by
  intro W
  let roots := g.sourceRootCells tops slope precision cutoff
  let f := fun c x => ((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) (fun _ => (a:ℂ)) a x 0 c
  have hfmeas (c : ℤ) : Measurable (f c) :=
    ((((g.measurable_mass tops slope precision cutoff weight hwmeas 0 c).pow_const a).complex_ofReal).smul
      (g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas K gap
        packets assigned stop value hv (fun _ => (a:ℂ)) a 0 c))
  have hfi (c : ℤ) (hc : c ∈ roots) : Integrable (f c) μ :=
    (integrable_norm_iff (hfmeas c).aestronglyMeasurable).mp (hrootInt c hc)
  have hi : Integrable (fun x => ∑ c ∈ roots, f c x) μ := integrable_finsetSum roots hfi
  have hni : Integrable (fun x => ∑ c ∈ roots, ‖f c x‖) μ :=
    integrable_finsetSum roots (fun c hc => (hfi c hc).norm)
  have heq : W = fun x => ∑ c ∈ roots, f c x := by
    funext x
    exact g.sourceBoundarySum_root_decomposition tops slope precision cutoff weight hp hw
      hK gap packets assigned stop (value x) hassigned heligible a x
  rw [heq]
  refine ⟨hi.norm,?_⟩
  calc
    _ ≤ ∫ x, ∑ c ∈ roots, ‖f c x‖ ∂μ :=
      integral_mono hi.norm hni (fun x => norm_sum_le _ _)
    _ = ∑ c ∈ roots, ∫ x, ‖f c x‖ ∂μ :=
      integral_finsetSum roots (fun c hc => (hfi c hc).norm)
    _ ≤ ∑ _c ∈ roots, B := Finset.sum_le_sum fun c hc => hrootBound c hc
    _ = (roots.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 2*B := mul_le_mul_of_nonneg_right
      (by exact_mod_cast g.sourceRootCells_card_le_two tops slope precision cutoff start hslope) hB

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTypeUniformCentral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical thresholds are chosen before all spatial and coefficient
index types. These are the existing source estimates with their universal
type binders moved inside the eventual statement; no bound changes. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
namespace AngularGrid
attribute [local instance] Classical.propDecidable
theorem eventually_source_central_sum_gain_types (d q Q : ℝ)
    (hd : 0 ≤ d) (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t, Measurable (weight t)) →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (start Nmass Fmass S : ℝ), 0 < Nmass → 0 < Fmass → 0 ≤ S →
      L/2 ≤ Real.log Nmass → μ.real Set.univ ≤ Fmass → S ≤ L^q*Nmass^2*Fmass →
      (∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) →
      (∀ᵐ x ∂μ, (∑ t ∈ tops, weight t x) ≤ L^q*Nmass) →
    let K := SourceParameters.blockCount L
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let beta := ((1+PhaseCombinatorics.phaseParameter D)/p)/(K:ℝ)
    let n := fun c => g.mass tops slope precision cutoff weight 0 c
    let amp := fun c x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) (fun _ => (beta:ℂ)) beta x 0 c
    (∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      Integrable (fun x => ‖(n c x^(alpha/p-1)) • amp c x‖^p) μ) →
    (∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      (∫ x, ‖(n c x^(alpha/p-1)) • amp c x‖^p ∂μ)^(1/p) ≤ L^q*S^(1/p)) →
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) beta x:ℝ):ℂ) • value x s
    Integrable (fun x => ‖W x‖) μ ∧ (∫ x, ‖W x‖ ∂μ) ≤ L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_source_central_integral_gain_ae d q (Q+1) hd hq (by positivity),
    eventually_ge_atTop (2:ℝ)] with L hgain hL
  intro τ σ X κ _ _ D hD hDL μ _ g tops slope precision cutoff weight hp hw hwmeas gap packets
    assigned stop value hv hassigned heligible start Nmass Fmass S hN hF hS hlogN
    hmeasure hSbound hslope htotal K p alpha beta n amp henergy hmoment W
  have hL0 : 0 < L := by linarith
  have hK : 0 < K := SourceParameters.blockCount_pos (by linarith)
  let B := L^(-(Q+1))*Nmass*Fmass
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hroot (c : ℤ) (hc : c ∈ g.sourceRootCells tops slope precision cutoff) :
      Integrable (fun x => n c x^beta*‖amp c x‖) μ ∧
        (∫ x, n c x^beta*‖amp c x‖ ∂μ) ≤ B := by
    have hnpos : ∀ x, 0 < n c x := by
      obtain ⟨t,ht⟩ := (g.mem_sourceRootCells tops slope precision cutoff c).mp hc
      intro x
      exact g.mass_pos_of_member tops slope precision cutoff weight hw 0 c x ht
    have hnupper : ∀ᵐ x ∂μ, n c x ≤ L^q*Nmass := by
      filter_upwards [htotal] with x hx
      exact (g.mass_le_total tops slope precision cutoff weight
        (fun t x => (hw t x).le) 0 c x).trans hx
    exact hgain D hD hDL X κ μ (n c) (amp c) Nmass Fmass S hN hF hS hlogN
      hnpos hnupper (g.measurable_mass tops slope precision cutoff weight hwmeas 0 c)
      (g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas K gap
        packets assigned stop value hv _ beta 0 c) hmeasure hSbound (henergy c hc) (hmoment c hc)
  have heq (c : ℤ) (x : X) :
      ‖((n c x^beta:ℝ):ℂ) • amp c x‖ = n c x^beta*‖amp c x‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg
        (g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le) 0 c x) _)]
  have hs := g.sourceBoundarySum_integral_le μ tops slope precision cutoff weight hp hw hwmeas
    hK gap packets assigned stop value hv hassigned heligible beta start B hB hslope
    (fun c hc => by
      change Integrable (fun x => ‖((n c x^beta:ℝ):ℂ) • amp c x‖) μ
      simpa only [heq] using (hroot c hc).1)
    (fun c hc => by
      change (∫ x, ‖((n c x^beta:ℝ):ℂ) • amp c x‖ ∂μ) ≤ B
      simpa only [heq] using (hroot c hc).2)
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hpower : 2*L^(-(Q+1)) ≤ L^(-Q) := by
    calc
      2*L^(-(Q+1)) ≤ L*L^(-(Q+1)) :=
        mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
      _ = L^(-Q) := by
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hL0]
        congr 1
        ring
  dsimp only [B]
  calc
    2*(L^(-(Q+1))*Nmass*Fmass) = (2*L^(-(Q+1)))*Nmass*Fmass := by ring
    _ ≤ L^(-Q)*Nmass*Fmass := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpower hN.le) hF.le

theorem eventually_source_central_from_paths_types_oai (q A B Pconst d m Q : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hqm : 2*q+2 ≤ m) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (μ : Measure X) (g : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (start Nmass Fmass : ℝ), 0 < Nmass → 0 < Fmass →
      L/2 ≤ Real.log Nmass → Real.log Nmass ≤ 2*L →
      (∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) →
    ∀ (good : Set X), MeasurableSet good →
    ∀ [IsFiniteMeasure (μ.restrict good)], (μ.restrict good).real univ ≤ Fmass →
      (∀ x ∈ good, (∑ t ∈ tops, weight t x) ≤ L^m*Nmass) →
    let S := ∑ t ∈ tops, ∫ x, weight t x ∂μ
    S ≤ L^m*Nmass^2*Fmass →
    ∀ (hK : 0 < SourceParameters.blockCount L),
    let K := SourceParameters.blockCount L
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let mu := PhaseCombinatorics.phaseMu D p
    let a := mu/(K:ℝ)
    let phase := fun (i : Fin K) (eta : Fin K → ℝ) (j : ℕ) =>
      phaseTubePoint (Pi.single i mu) eta (ShiftedBlocks.tag hK j)
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ (i : Fin K) eta x, x ∈ good → ∀ c,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (phase i eta) a x 0 c‖ ≤
        L^(2*q)*(1+Real.sqrt (∑ j, (eta j)^2))*g.mass tops slope precision cutoff weight 0 c x) →
    ∀ (count : Fin K → ℕ) (bad : Fin K → (Fin K → ℝ) → τ → Set X),
      (∀ i, ∀ t ∈ tops, ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint i (count i))) →
    (∀ i eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∀ x ∈ good, ∀ j ≤ count i, ∀ c,
        ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (phase i eta) a x (ShiftedBlocks.endpoint i j) c‖ ≤
          L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint i j) c x) ∧
      (∀ x ∈ good, cost*(∑ t ∈ tops.filter (fun t => x ∈ bad i eta t), weight t x) ≤ 1/2) ∧
      (∀ t ∈ tops, Integrable ((good\bad i eta t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          (phase i eta) a alpha p (L^A) i t (count i) x)) μ) ∧
      (∀ t ∈ tops, (∫ x, (good\bad i eta t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          (phase i eta) a alpha p (L^A) i t (count i) x) x ∂μ) ≤
        Pconst*L^B*cost*(∫ x, weight t x ∂μ))) →
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x:ℝ):ℂ) • value x s
    IntegrableOn (fun x => ‖W x‖) good μ ∧
      (∫ x in good, ‖W x‖ ∂μ) ≤ L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_source_root_diagonal_from_paths_types
      q A B Pconst hq hA hB hP,
    eventually_source_central_sum_gain_types
      d m Q hd hm hQ,
    eventually_source_polynomial_mass_log m,eventually_ge_atTop (256:ℝ)]
    with L hroot hcentral hlogmass hL
  intro τ σ X κ _ _ D hD hDL μ g tops slope precision cutoff weight hp hw hwint hwmeas gap packets assigned
    stop value hv hassigned heligible start Nmass Fmass hN hF hloglo hloghi hslope good hgood _
    hmeasure htotal S hSbound hK K p alpha mu a phase cost hcrude count bad hterminal hpaths W
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hp0 : 0 < p := Real.sqrt_pos.mpr hL0
  have halpha : 1 ≤ alpha ∧ alpha ≤ 3 := by
    have htheta := PhaseCombinatorics.phaseParameter_range hD
    change 0 < PhaseCombinatorics.phaseParameter D ∧ PhaseCombinatorics.phaseParameter D ≤ 1/3 at htheta
    dsimp only [alpha]
    constructor <;> linarith [htheta.1,htheta.2]
  have hmu := source_phaseMu_small hD hL
  have hSn : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have hr (c : ℤ) (hc : c ∈ g.sourceRootCells tops slope precision cutoff) := by
    have hrmem {t : τ} (ht : t ∈ g.cellTops tops slope precision cutoff 0 c) : t ∈ tops :=
      ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1
    exact hroot τ σ X κ μ g tops slope precision cutoff weight hp hw hwint hwmeas K hK gap packets
      assigned stop value hv hassigned heligible c good hgood (L^m*Nmass) a alpha mu
      (by positivity) halpha.1 halpha.2 hmu.1.le (hmu.2.trans (by norm_num))
      (hlogmass Nmass hN hloghi) ((g.mem_sourceRootCells tops slope precision cutoff c).mp hc)
      (fun x hx => (g.mass_le_total tops slope precision cutoff weight
        (fun t x => (hw t x).le) 0 c x).trans (htotal x hx))
      (fun i eta x hx => hcrude i eta x hx c) count bad
      (fun i t ht => hterminal i t (hrmem ht))
      (fun i eta heta => by
        obtain ⟨henv,hbad,hpi,hpb⟩ := hpaths i eta heta
        refine ⟨henv,?_,fun t ht => hpi t (hrmem ht),fun t ht => hpb t (hrmem ht)⟩
        intro x hx
        apply (mul_le_mul_of_nonneg_left ?_ hcost).trans (hbad x hx)
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (fun t ht => hrmem ht))
          (fun t _ _ => (hw t x).le))
  have hmoment (c : ℤ) (hc : c ∈ g.sourceRootCells tops slope precision cutoff) :
      (∫ x in good, ‖(g.mass tops slope precision cutoff weight 0 c x^(alpha/p-1)) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (fun _ => (a:ℂ)) a x 0 c‖^p ∂μ)^(1/p) ≤ L^m*S^(1/p) := by
    have hb := (hr c hc).2
    simp only [sourceShiftFamily,phaseTubePoint,Complex.ofReal_zero,zero_mul,add_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL1 hqm) (Real.rpow_nonneg hSn _))
  have hi := hcentral τ σ X κ D hD hDL (μ.restrict good) g tops slope precision cutoff weight hp hw hwmeas
    gap packets assigned stop value hv hassigned heligible start Nmass Fmass S hN hF hSn
    hloglo hmeasure hSbound hslope (by
      filter_upwards [ae_restrict_mem hgood] with x hx
      exact htotal x hx)
    (fun c hc => by
      have hh := (hr c hc).1
      simpa only [p,K,alpha,mu,a,IntegrableOn,PhaseCombinatorics.phaseMu,sourceShiftFamily,phaseTubePoint,Complex.ofReal_zero,zero_mul,add_zero] using hh)
    hmoment
  exact hi

end AngularGrid
end LipschitzHilbert

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types_oai.{u_1, u_2, u_3} := @OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types_oai.{u_1, u_2, u_3}
