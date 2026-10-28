-- Prove2me | solution 1 for OAI.RowColumn.occupied_overlap_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:01:49.461192+00:00
-- url     : https://prove2.me/submissions/2f4a97b2-f9f1-477a-9aac-9e408b704f32

import Mathlib
import Definitions.Def_OccupiedOverlap
import Definitions.Def_OAIW2RC000
import Theorems.Thm_OAI_RowColumn_occupied_dimension_ratio

section
-- module Solutions.OAIW2_RowColumn.Compat
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Uncertainty
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]

lemma act_single [DecidableEq X] (p : Equiv.Perm X) (x : X) :
    act p (EuclideanSpace.single x (1:ℂ)) = EuclideanSpace.single (p x) 1 := by
  exact EuclideanSpace.piLpCongrLeft_single p x 1

lemma trace_projection (W : Submodule ℂ (H X)) :
    ∑ x, (W.starProjection (EuclideanSpace.single x (1:ℂ))) x = Module.finrank ℂ W := by
  classical
  have hp : LinearMap.IsProj W W.starProjection.toLinearMap := by
    constructor
    · intro x; exact (W.orthogonalProjectionOnto x).2
    · intro x hx; exact W.starProjection_eq_self_iff.mpr hx
  have ht := hp.trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun X ℂ).toBasis] at ht
  simpa only [Matrix.trace,Matrix.diag_apply,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,ContinuousLinearMap.coe_coe] using ht

lemma projection_diagonal (W : Submodule ℂ (H X)) (x : X) :
    (W.starProjection (EuclideanSpace.single x (1:ℂ))) x =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
  classical
  have hh := W.inner_starProjection_left_eq_right
    (EuclideanSpace.single x (1:ℂ)) (W.starProjection (EuclideanSpace.single x (1:ℂ)))
  have hf : W.starProjection (W.starProjection (EuclideanSpace.single x (1:ℂ))) =
      W.starProjection (EuclideanSpace.single x (1:ℂ)) :=
    W.starProjection_eq_self_iff.mpr (W.orthogonalProjectionOnto _).2
  rw [hf] at hh
  rw [inner_self_eq_norm_sq_to_K,EuclideanSpace.inner_single_left] at hh
  simpa using hh.symm

lemma projection_comm (W : Submodule ℂ (H X)) (p : Equiv.Perm X)
    (hW : W.map (act p).toLinearEquiv.toLinearMap = W) (v : H X) :
    act p (W.starProjection v) = W.starProjection (act p v) := by
  have hh := (act p).toLinearIsometry.map_starProjection W v
  change act p (W.starProjection v) =
    (W.map (act p).toLinearEquiv.toLinearMap).starProjection (act p v) at hh
  simpa only [hW] using hh

/-- A transitive invariant subspace has constant diagonal orthogonal projection. -/
lemma uniform_diagonal (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W) (x : X) :
    (Fintype.card X:ℝ) * ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 =
      Module.finrank ℂ W := by
  classical
  have hh (y : X) : (W.starProjection (EuclideanSpace.single y (1:ℂ))) y =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
    obtain ⟨p,hp,hW⟩ := htrans x y
    subst y
    rw [projection_diagonal,←act_single p x,←projection_comm W p hW,(act p).norm_map]
  have ht := trace_projection W
  simp_rw [hh] at ht
  have hhreal : (∑ _y : X, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2) =
      (Module.finrank ℂ W:ℝ) := by exact_mod_cast ht
  simpa using hhreal

/-- The uncertainty bound, with no assumption of irreducibility. -/
theorem uncertainty (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (v : H X) (hv : v ∈ W) (x : X) :
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤ (Module.finrank ℂ W:ℝ) * ‖v‖^2 := by
  classical
  have hh : inner ℂ (W.starProjection (EuclideanSpace.single x (1:ℂ))) v = v x := by
    rw [W.inner_starProjection_left_eq_right,W.starProjection_eq_self_iff.mpr hv,
      EuclideanSpace.inner_single_left]
    simp
  have hc := norm_inner_le_norm (𝕜 := ℂ) (W.starProjection (EuclideanSpace.single x (1:ℂ))) v
  rw [hh] at hc
  have hs : ‖v x‖^2 ≤ ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2 := by
    nlinarith [norm_nonneg (v x),norm_nonneg v,
      norm_nonneg (W.starProjection (EuclideanSpace.single x (1:ℂ)))]
  calc
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤
      (Fintype.card X:ℝ) * (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by rw [←mul_assoc,uniform_diagonal W htrans x]

end CubeShuffle.PermutationHilbert

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.YoungSymmetry_Polytabloid
attribute [-instance] _root_.OAI.CubeShuffle.Specht.tabloidMulAction _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary polytabloid input for the symmetric-group step of FAC.7.
No branching or classification theorem is postulated here. -/
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma strictMono_fin_nat_ge {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) :
    ∀ i, i.val ≤ f i := by
  intro i
  induction h : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hn : n = 0
    · omega
    · have hn' : n-1 < i.val := by omega
      let j : Fin _ := ⟨n-1, hn'.trans i.isLt⟩
      have hj := ih (n-1) (by omega) j rfl
      have hij := hf (show j < i from hn')
      dsimp [j] at hj hij
      omega

lemma rankCell_row_le {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) :
    row (rankCell f hf x) ≤ f x := by
  rw [←rankCell_orderEmb f hf x]
  exact strictMono_fin_nat_ge _ (OrderEmbedding.strictMono _) _

/-- The equal-shape column-transporter lemma. This is the combinatorial rank-one
input to the Specht submodule theorem, proved using sorting, not Young's rule. -/
theorem column_transporter (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (hp : ∀ x y, col x = col y → row (p x) = row (p y) → x = y) :
    ∃ c : Equiv.Perm (Cell μ), (∀ x, col (c x) = col x) ∧
      ∀ x, row (c x) = row (p x) := by
  classical
  let c := rankPerm (fun x => row (p x)) hp
  refine ⟨c, fun x => rfl, ?_⟩
  have hle (x : Cell μ) : row (c x) ≤ row (p x) := rankCell_row_le _ hp x
  have hsum : ∑ x, row (c x) = ∑ x, row (p x) := by
    rw [Equiv.sum_comp, Equiv.sum_comp]
  exact fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).mp hsum x (Finset.mem_univ _)

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma tabloidRep_delta {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) (f : Tabloid μ) :
    tabloidRep μ p (delta f) = delta (tabloidAct p f) := by
  classical
  ext g
  simp only [tabloidRep_apply,delta,Equiv.Perm.inv_def]
  congr 1
  exact propext (Equiv.symm_apply_eq (tabloidAct p))

lemma colGroup_row_stabilizer {μ : YoungDiagram} (c : colGroup μ)
    (hc : tabloidAct c (baseTabloid μ) = baseTabloid μ) : (c : Equiv.Perm (Cell μ)) = 1 := by
  apply Equiv.ext
  intro x
  have hr := congrArg (fun f : Tabloid μ => ((f.1 ((c : Equiv.Perm _) x)) : ℕ)) hc
  simp only [tabloidAct_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply,baseTabloid,rowIndex] at hr
  apply Subtype.ext
  exact Prod.ext hr.symm (c.2 x)

lemma tabloid_column_transporter {μ : YoungDiagram} (f : Tabloid μ)
    (hf : ∀ x y, col x = col y → f.1 x = f.1 y → x = y) :
    ∃ c : colGroup μ, f = tabloidAct c (baseTabloid μ) := by
  obtain ⟨p,hp⟩ := f.2
  have hp' : ∀ x y, col x = col y → row (p x) = row (p y) → x = y := by
    intro x y hcol hrow
    apply hf x y hcol
    rw [hp]
    exact Fin.ext hrow
  obtain ⟨c,hcol,hrow⟩ := column_transporter μ p hp'
  refine ⟨⟨c⁻¹, (colGroup μ).inv_mem hcol⟩, ?_⟩
  apply Subtype.ext
  funext x
  apply Fin.ext
  simp only [tabloidAct_apply,baseTabloid,rowIndex,inv_inv,hp,Function.comp_apply]
  exact (hrow x).symm

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma permSign_sq {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    permSign p * permSign p = 1 := by
  calc
    permSign p * permSign p = permSign (p*p⁻¹) := by rw [permSign_mul,permSign_inv]
    _ = 1 := by simp

section Alternator
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

lemma alternator_mul (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) :
    alternator C ρ * ρ c = permSign (c : Equiv.Perm α) • alternator C ρ := by
  classical
  rw [alternator,Finset.sum_mul,Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulRight c)
  intro a
  simp only [smul_mul_assoc,←map_mul,Equiv.coe_mulRight,Subgroup.coe_mul,permSign_mul,smul_smul]
  congr 1
  have h := permSign_sq (c : Equiv.Perm α)
  calc
    permSign (a : Equiv.Perm α) = permSign (a : Equiv.Perm α)*1 := by ring
    _ = permSign (a : Equiv.Perm α)*(permSign (c : Equiv.Perm α)*permSign (c : Equiv.Perm α)) := by rw [h]
    _ = _ := by ring

lemma mul_alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) :
    ρ c * alternator C ρ = permSign (c : Equiv.Perm α) • alternator C ρ := by
  classical
  rw [alternator,Finset.mul_sum,Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro a
  simp only [mul_smul_comm,←map_mul,Equiv.coe_mulLeft,Subgroup.coe_mul,permSign_mul,smul_smul]
  congr 1
  have h := permSign_sq (c : Equiv.Perm α)
  calc
    permSign (a : Equiv.Perm α) = 1*permSign (a : Equiv.Perm α) := by ring
    _ = (permSign (c : Equiv.Perm α)*permSign (c : Equiv.Perm α))*permSign (a : Equiv.Perm α) := by rw [h]
    _ = _ := by ring

lemma alternator_apply_action (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V) :
    alternator C ρ (ρ c v) = permSign (c : Equiv.Perm α) • alternator C ρ v := by
  exact congrArg (fun T : Module.End ℂ V => T v) (alternator_mul C ρ c)

lemma action_alternator_apply (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V) :
    ρ c (alternator C ρ v) = permSign (c : Equiv.Perm α) • alternator C ρ v := by
  exact congrArg (fun T : Module.End ℂ V => T v) (mul_alternator C ρ c)

/-- An odd column stabilizer forces cancellation in the genuine alternating sum. -/
lemma alternator_eq_zero_of_odd_stabilizer (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V)
    (hc : permSign (c : Equiv.Perm α) = -1) (hv : ρ c v = v) :
    alternator C ρ v = 0 := by
  have h := alternator_apply_action C ρ c v
  rw [hv,hc,neg_one_smul] at h
  have h2 : (2:ℂ) • alternator C ρ v = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end Alternator
end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma swap_mem_colGroup {μ : YoungDiagram} (x y : Cell μ) (hc : col x = col y) :
    Equiv.swap x y ∈ colGroup μ := by
  classical
  intro z
  by_cases hx : z=x
  · subst z; simpa using hc.symm
  by_cases hy : z=y
  · subst z; simpa using hc
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma swap_fixes_tabloid {μ : YoungDiagram} (f : Tabloid μ) (x y : Cell μ)
    (hxy : f.1 x = f.1 y) : tabloidAct (Equiv.swap x y) f = f := by
  classical
  apply Subtype.ext
  funext z
  simp only [tabloidAct_apply, Equiv.swap_inv]
  by_cases hx : z=x
  · subst z; simpa using hxy.symm
  by_cases hy : z=y
  · subst z; simpa using hxy
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma alternator_delta_rank_one {μ : YoungDiagram} (f : Tabloid μ) :
    ∃ z : ℂ, alternator (colGroup μ) (tabloidRep μ) (delta f) = z • polytabloid μ := by
  classical
  by_cases hf : ∀ x y, col x = col y → f.1 x = f.1 y → x = y
  · obtain ⟨c,rfl⟩ := tabloid_column_transporter f hf
    refine ⟨permSign (c:Equiv.Perm (Cell μ)), ?_⟩
    rw [←tabloidRep_delta]
    exact alternator_apply_action _ _ c _
  · push Not at hf
    obtain ⟨x,y,hcol,hrow,hne⟩ := hf
    refine ⟨0, ?_⟩
    rw [zero_smul]
    apply alternator_eq_zero_of_odd_stabilizer _ _ ⟨Equiv.swap x y,swap_mem_colGroup x y hcol⟩
    · exact permSign_swap hne
    · rw [tabloidRep_delta,swap_fixes_tabloid f x y hrow]

lemma polytabloid_formula (μ : YoungDiagram) :
    polytabloid μ = ∑ c : colGroup μ, permSign (c:Equiv.Perm (Cell μ)) •
      delta (tabloidAct c (baseTabloid μ)) := by
  classical
  simp only [polytabloid,alternator,LinearMap.sum_apply,LinearMap.smul_apply,tabloidRep_delta]

lemma polytabloid_base (μ : YoungDiagram) : polytabloid μ (baseTabloid μ) = 1 := by
  classical
  rw [polytabloid_formula,Finset.sum_apply]
  rw [Finset.sum_eq_single (1 : colGroup μ)]
  · simp [delta]
  · intro c hc hne
    have hn : baseTabloid μ ≠ tabloidAct c (baseTabloid μ) := by
      intro h
      apply hne
      exact Subtype.ext (colGroup_row_stabilizer c h.symm)
    simp [Pi.smul_apply,delta,hn]
  · simp

lemma polytabloid_ne_zero (μ : YoungDiagram) : polytabloid μ ≠ 0 := by
  intro h
  have hv := congrArg (fun v : Tabloid μ → ℂ => v (baseTabloid μ)) h
  simp [polytabloid_base] at hv

lemma delta_decomposition {μ : YoungDiagram} (v : Tabloid μ → ℂ) :
    v = ∑ f : Tabloid μ, v f • delta f := by
  classical
  funext g
  simp only [Finset.sum_apply,Pi.smul_apply,delta,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp

/-- The actual column antisymmetrizer has one-dimensional range. -/
theorem alternator_rank_one (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    ∃ z : ℂ, alternator (colGroup μ) (tabloidRep μ) v = z • polytabloid μ := by
  classical
  choose z hz using fun f : Tabloid μ => alternator_delta_rank_one f
  refine ⟨∑ f, v f * z f, ?_⟩
  conv_lhs => rw [delta_decomposition v]
  simp only [map_sum,map_smul,hz,smul_smul,Finset.sum_smul]

lemma alternator_rank_one_exact (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v =
      (alternator (colGroup μ) (tabloidRep μ) v (baseTabloid μ)) • polytabloid μ := by
  obtain ⟨z,hz⟩ := alternator_rank_one μ v
  rw [hz]
  simp only [Pi.smul_apply,polytabloid_base,smul_eq_mul,mul_one]

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma pairing_delta {μ : YoungDiagram} (f : Tabloid μ) (v : Tabloid μ → ℂ) :
    pairing (delta f) v = v f := by
  classical
  simp [pairing,delta]

lemma pairing_sum_left {μ : YoungDiagram} {ι : Type*} [Fintype ι]
    (v : ι → Tabloid μ → ℂ) (w : Tabloid μ → ℂ) :
    pairing (∑ i, v i) w = ∑ i, pairing (v i) w := by
  simp only [pairing,Finset.sum_apply,map_sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma pairing_smul_left {μ : YoungDiagram} (a : ℂ) (v w : Tabloid μ → ℂ) :
    pairing (a • v) w = starRingEnd ℂ a * pairing v w := by
  simp only [pairing,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  ring

lemma pairing_zero_left {μ : YoungDiagram} (v : Tabloid μ → ℂ) : pairing 0 v = 0 := by
  simp [pairing]

lemma pairing_add_left {μ : YoungDiagram} (u v w : Tabloid μ → ℂ) :
    pairing (u+v) w = pairing u w + pairing v w := by
  simp [pairing,mul_add,Finset.sum_add_distrib]

lemma pairing_self_eq_zero {μ : YoungDiagram} (v : Tabloid μ → ℂ) :
    pairing v v = 0 ↔ v = 0 := by
  change inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ (Tabloid μ)) (WithLp.toLp 2 v) = 0 ↔ v = 0
  rw [inner_self_eq_zero]
  constructor
  · intro h; exact congrArg WithLp.ofLp h
  · intro h; subst v; rfl

lemma pairing_action {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) (v w : Tabloid μ → ℂ) :
    pairing (tabloidRep μ p v) w = pairing v (tabloidRep μ p⁻¹ w) := by
  classical
  simp only [pairing,tabloidRep_apply,inv_inv]
  apply Fintype.sum_equiv (tabloidAct p⁻¹)
  intro f
  have hcancel : tabloidAct p (tabloidAct p⁻¹ f) = f := by
    rw [tabloidAct_inv]
    exact (tabloidAct p).apply_symm_apply f
  rw [hcancel]

lemma alternator_base_pairing (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v (baseTabloid μ) = pairing (polytabloid μ) v := by
  classical
  simp only [polytabloid_formula,pairing_sum_left,pairing_smul_left,conj_permSign,pairing_delta]
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,tabloidRep_apply]
  apply Fintype.sum_equiv (Equiv.inv (colGroup μ))
  intro c
  simp only [Equiv.inv_apply,Subgroup.coe_inv,permSign_inv]

/-- The column antisymmetrizer is the rank-one form of the polytabloid. -/
theorem alternator_pairing (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v = pairing (polytabloid μ) v • polytabloid μ := by
  rw [alternator_rank_one_exact,alternator_base_pairing]

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma polytabloid_mem_space (μ : YoungDiagram) : polytabloid μ ∈ space μ := by
  simpa using orbit_mem_space μ 1

lemma alternator_mem_invariant (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) (v : Tabloid μ → ℂ) (hv : v ∈ W) :
    alternator (colGroup μ) (tabloidRep μ) v ∈ W := by
  classical
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply]
  exact W.sum_mem (fun c _ => W.smul_mem _ (hW c v hv))

/-- The Specht submodule theorem, for the actual complex tabloid module. -/
theorem submodule_theorem (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) :
    space μ ≤ W ∨ ∀ v ∈ W, ∀ w ∈ space μ, pairing w v = 0 := by
  classical
  by_cases hSW : space μ ≤ W
  · exact Or.inl hSW
  right
  have he : polytabloid μ ∉ W := by
    intro he
    apply hSW
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact hW p _ he
  have hpair : ∀ v ∈ W, pairing (polytabloid μ) v = 0 := by
    intro v hv
    by_contra hne
    apply he
    have hal := alternator_mem_invariant μ W hW v hv
    rw [alternator_pairing] at hal
    have hh := W.smul_mem (pairing (polytabloid μ) v)⁻¹ hal
    simpa only [smul_smul,inv_mul_cancel₀ hne,one_smul] using hh
  intro v hv w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p,rfl⟩ := hw
    rw [pairing_action]
    exact hpair _ (hW p⁻¹ v hv)
  | zero => exact pairing_zero_left v
  | add u w hu hw ihu ihw => rw [pairing_add_left,ihu,ihw,add_zero]
  | smul a w hw ih => rw [pairing_smul_left,ih,mul_zero]

/-- No proper nonzero invariant complex subspace exists in a Specht space. -/
theorem space_simple (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) (hWS : W ≤ space μ) :
    W = ⊥ ∨ W = space μ := by
  obtain hSW | horth := submodule_theorem μ W hW
  · exact Or.inr (le_antisymm hWS hSW)
  · left
    apply le_antisymm _ bot_le
    intro v hv
    exact (pairing_self_eq_zero v).mp (horth v hv v (hWS hv))

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

/-- The constructed Specht representation is irreducible over the complex numbers. -/
theorem representation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (representation μ) := by
  have hnt : (⊥ : Subrepresentation (representation μ)) ≠ ⊤ := by
    intro h
    have he : (⟨polytabloid μ,polytabloid_mem_space μ⟩ : space μ) ∈
        (⊥ : Subrepresentation (representation μ)) := by rw [h]; trivial
    have he' : (⟨polytabloid μ,polytabloid_mem_space μ⟩ : space μ) = 0 := he
    exact polytabloid_ne_zero μ (congrArg Subtype.val he')
  refine { exists_pair_ne := ⟨⊥,⊤,hnt⟩, eq_bot_or_eq_top := ?_ }
  intro U
  let W : Submodule ℂ (Tabloid μ → ℂ) := U.toSubmodule.map (space μ).subtype
  have hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W := by
    intro p v hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact ⟨representation μ p u,U.apply_mem_toSubmodule p hu,rfl⟩
  have hWS : W ≤ space μ := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact u.2
  obtain hbot | htop := space_simple μ W hW hWS
  · left
    apply le_antisymm _ bot_le
    intro u hu
    have hmem : (u : Tabloid μ → ℂ) ∈ W := ⟨u,hu,rfl⟩
    rw [hbot,Submodule.mem_bot] at hmem
    change u = 0
    exact Subtype.ext hmem
  · right
    apply le_antisymm le_top
    intro u hu
    have hmem : (u : Tabloid μ → ℂ) ∈ W := by rw [htop]; exact u.2
    obtain ⟨v,hv,hvu⟩ := hmem
    have heq : v = u := Subtype.ext hvu
    exact heq ▸ hv

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.YoungSymmetry_Dimensions
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma finrank_hilbertSpace (μ : YoungDiagram) :
    Module.finrank ℂ (hilbertSpace μ) = Module.finrank ℂ (space μ) :=
  (hilbertEquiv μ).finrank_map_eq (space μ)

lemma hilbert_action (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) (v : Tabloid μ → ℂ) :
    hilbertEquiv μ (tabloidRep μ p v) =
      PermutationHilbert.act (tabloidAct p) (hilbertEquiv μ v) := by
  ext f
  simp [hilbertEquiv,PermutationHilbert.act_apply]

lemma hilbertSpace_invariant (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) :
    (hilbertSpace μ).map (PermutationHilbert.act (tabloidAct p)).toLinearEquiv.toLinearMap =
      hilbertSpace μ := by
  apply le_antisymm
  · rintro _ ⟨v,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨tabloidRep μ p w,action_mem_space μ p w hw,hilbert_action μ p w⟩
  · rintro _ ⟨w,hw,rfl⟩
    refine ⟨hilbertEquiv μ (tabloidRep μ p⁻¹ w),
      ⟨tabloidRep μ p⁻¹ w,action_mem_space μ p⁻¹ w hw,rfl⟩, ?_⟩
    change PermutationHilbert.act (tabloidAct p) (hilbertEquiv μ (tabloidRep μ p⁻¹ w)) = hilbertEquiv μ w
    rw [←hilbert_action]
    change hilbertEquiv μ ((tabloidRep μ p * tabloidRep μ p⁻¹) w) = _
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl

lemma tabloidAct_transitive (μ : YoungDiagram) (f g : Tabloid μ) :
    ∃ p : Equiv.Perm (Cell μ), tabloidAct p f = g := by
  obtain ⟨q,hq⟩ := f.2
  obtain ⟨r,hr⟩ := g.2
  refine ⟨r⁻¹*q, ?_⟩
  apply Subtype.ext
  funext x
  simp only [tabloidAct_apply,mul_inv_rev,Equiv.Perm.mul_apply,hq,hr,
    Function.comp_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply,Equiv.symm_symm]

lemma polytabloid_pairing (μ : YoungDiagram) :
    pairing (polytabloid μ) (polytabloid μ) = Fintype.card (colGroup μ) := by
  have h := alternator_pairing μ (polytabloid μ)
  have he (c : colGroup μ) : tabloidRep μ c (polytabloid μ) =
      permSign (c:Equiv.Perm (Cell μ)) • polytabloid μ :=
    action_alternator_apply (colGroup μ) (tabloidRep μ) c _
  have hb := congrArg (fun v : Tabloid μ → ℂ => v (baseTabloid μ)) h
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,he,
    Pi.smul_apply,smul_eq_mul,Finset.sum_apply,polytabloid_base,mul_one] at hb
  simp only [permSign_sq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  exact hb.symm

lemma polytabloid_norm_sq (μ : YoungDiagram) :
    ‖hilbertEquiv μ (polytabloid μ)‖^2 = (Fintype.card (colGroup μ):ℝ) := by
  have hp := polytabloid_pairing μ
  change inner ℂ (hilbertEquiv μ (polytabloid μ)) (hilbertEquiv μ (polytabloid μ)) = _ at hp
  rw [inner_self_eq_norm_sq_to_K] at hp
  have hre := congrArg Complex.re hp
  simpa [pow_two] using hre

/-- The genuine Specht dimension bound obtained from uncertainty in the
transitive tabloid module; no hook formula or tableau spanning assumption. -/
theorem dimension_times_column_ge_tabloids (μ : YoungDiagram) :
    Fintype.card (Tabloid μ) ≤ Module.finrank ℂ (space μ) * Fintype.card (colGroup μ) := by
  have ht (f g : Tabloid μ) : ∃ p : Equiv.Perm (Tabloid μ), p f = g ∧
      (hilbertSpace μ).map (PermutationHilbert.act p).toLinearEquiv.toLinearMap = hilbertSpace μ := by
    obtain ⟨p,hp⟩ := tabloidAct_transitive μ f g
    exact ⟨tabloidAct p,hp,hilbertSpace_invariant μ p⟩
  have hu := PermutationHilbert.uncertainty (hilbertSpace μ) ht
    (hilbertEquiv μ (polytabloid μ)) ⟨polytabloid μ,polytabloid_mem_space μ,rfl⟩ (baseTabloid μ)
  have he : hilbertEquiv μ (polytabloid μ) (baseTabloid μ) = 1 := polytabloid_base μ
  rw [he,norm_one,one_pow,mul_one,finrank_hilbertSpace,polytabloid_norm_sq] at hu
  exact_mod_cast hu

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma tabloid_orbit_all (μ : YoungDiagram) :
    MulAction.orbit (Equiv.Perm (Cell μ)) (baseTabloid μ) = Set.univ := by
  ext f
  simp only [Set.mem_univ,iff_true]
  obtain ⟨p,hp⟩ := tabloidAct_transitive μ (baseTabloid μ) f
  exact ⟨p,hp⟩

lemma tabloid_stabilizer (μ : YoungDiagram) :
    MulAction.stabilizer (Equiv.Perm (Cell μ)) (baseTabloid μ) = rowGroup μ := by
  ext p
  change tabloidAct p (baseTabloid μ) = baseTabloid μ ↔ ∀ x, rowIndex (p x) = rowIndex x
  constructor
  · intro h x
    have hh := congrArg (fun f : Tabloid μ => f.1 (p x)) h
    simpa only [tabloidAct_apply,baseTabloid,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using hh.symm
  · intro h
    apply Subtype.ext
    funext x
    exact (h (p⁻¹ x)).symm.trans (by simp [baseTabloid])

lemma card_tabloid_mul_row (μ : YoungDiagram) :
    Fintype.card (Tabloid μ)*Fintype.card (rowGroup μ) = μ.card.factorial := by
  have hh := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Equiv.Perm (Cell μ)) (baseTabloid μ)
  have hc : Fintype.card (MulAction.orbit (Equiv.Perm (Cell μ)) (baseTabloid μ)) =
      Fintype.card (Tabloid μ) := by
    rw [tabloid_orbit_all,Fintype.card_setUniv]
  simpa only [hc,tabloid_stabilizer,Fintype.card_perm,card_cell] using hh

/-- Fully algebraic factorial/product lower bound for the actual irreducible dimension. -/
theorem factorial_le_dimension_row_column (μ : YoungDiagram) :
    μ.card.factorial ≤ Module.finrank ℂ (space μ)*Fintype.card (rowGroup μ)*Fintype.card (colGroup μ) := by
  rw [←card_tabloid_mul_row]
  nlinarith [dimension_times_column_ge_tabloids μ]

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.YoungSymmetry_UnitaryModel
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma unitaryRepresentation_coe (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : hilbertSpace μ) :
    (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ)) =
      PermutationHilbert.act (tabloidAct p) v := by
  obtain ⟨w,rfl⟩ := (spaceHilbertEquiv μ).surjective v
  change hilbertEquiv μ (tabloidRep μ p w) = _
  exact hilbert_action μ p w

lemma unitaryRepresentation_unitary (μ : YoungDiagram) :
    UnitaryFinite.IsUnitary (G := Equiv.Perm (Cell μ)) (V := hilbertSpace μ) (unitaryRepresentation μ) := by
  intro p v w
  change inner ℂ (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ))
      (unitaryRepresentation μ p w : PermutationHilbert.H (Tabloid μ)) = _
  rw [unitaryRepresentation_coe,unitaryRepresentation_coe]
  exact (PermutationHilbert.act (tabloidAct p)).inner_map_map v w

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma relabelledUnitary_unitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    UnitaryFinite.IsUnitary (V := hilbertSpace μ) (relabelledUnitary μ e) := by
  intro g v w
  exact unitaryRepresentation_unitary μ (e.permCongr g) v w

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.CubeShuffle_ShapeSpectral
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical
open UnitaryFinite Filter

lemma dimension_pos (μ : YoungDiagram) : 0 < Module.finrank ℂ (space μ) := by
  have h := factorial_le_dimension_row_column μ
  by_contra hn
  have hz : Module.finrank ℂ (space μ)=0 := by omega
  rw [hz,zero_mul,zero_mul] at h
  exact (Nat.factorial_pos μ.card).not_ge h

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_SignedWords
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma word_stabilizer_eq (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (x : S) : w.1 (g x) = w.1 x := by
  have he := congrArg (fun z : Words (S := S) odd k => z.1 (g x)) hw
  simpa using he.symm

omit [Fintype C] [DecidableEq C] in
lemma oddPerm_sign_of_stabilizes (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (hfix : ∀ x, ¬ odd (w.1 x) → g x = x) :
    permSign (oddPerm g w) = permSign g := by
  have hs : ∀ x, odd (w.1 (g x)) ↔ odd (w.1 x) := fun x => by
    rw [word_stabilizer_eq g w hw x]
  have he := Equiv.Perm.sign_eq_sign_of_equiv (g.subtypePerm hs)
    (oddPerm g w) (oddFrame w) (by
      intro x
      change oddFrame w ⟨g x.1, _⟩ =
        oddFrame (actWord g w)
          ((relabelOddEquiv g w.1) ((oddFrame w).symm (oddFrame w x)))
      erw [Equiv.symm_apply_apply]
      exact (oddFrame_congr hw (g x.1) _ _).symm)
  have hf : ∀ x, g x ≠ x → odd (w.1 x) := by
    intro x hn
    by_contra h
    exact hn (hfix x h)
  rw [Equiv.Perm.sign_subtypePerm g hs hf] at he
  exact congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)) he.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_of_odd_fixed (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (hfix : ∀ x, odd (w.1 x) → g x = x) :
    oddPerm g w = 1 := by
  apply Equiv.ext
  intro i
  let x := (oddFrame w).symm i
  change oddFrame (actWord g w) ⟨g x.1, _⟩ = i
  have he := oddFrame_congr hw (g x.1)
    (show odd ((actWord g w).1 (g x.1)) by simpa using x.2)
    (by rw [hfix x.1 x.2]; exact x.2)
  refine he.trans ?_
  have hh : (⟨g x.1, by rw [hfix x.1 x.2]; exact x.2⟩ : OddSlots w) = x :=
    Subtype.ext (hfix x.1 x.2)
  rw [hh]
  exact (oddFrame w).apply_symm_apply i

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma actWord_inv_eq_iff (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    actWord g⁻¹ w = w ↔ actWord g w = w := by
  constructor
  · intro he
    have hh := congrArg (actWord g) he
    rw [← actWord_mul, mul_inv_cancel, actWord_one] at hh
    exact hh.symm
  · intro he
    have hh := congrArg (actWord g⁻¹) he
    rw [← actWord_mul, inv_mul_cancel, actWord_one] at hh
    exact hh.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_inv_stabilizer (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) : oddPerm g⁻¹ w = (oddPerm g w)⁻¹ := by
  have hh := oddPerm_mul g⁻¹ g w
  rw [inv_mul_cancel, oddPerm_one, hw] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

omit [DecidableEq S] [Fintype C] in
lemma wordVector_coefficient (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    Signed.representation g (wordVector w) w =
      if actWord g w = w then permSign (oddPerm g w) else 0 := by
  change permSign (oddPerm g⁻¹ w) * (if actWord g⁻¹ w = w then (1 : ℂ) else 0) = _
  simp only [actWord_inv_eq_iff]
  split_ifs with he
  · rw [oddPerm_inv_stabilizer g w he, permSign_inv, mul_one]
  · exact mul_zero _

end RowColumn.Signed

namespace RowColumn.Signed
open CubeShuffle.Specht
open scoped BigOperators Classical

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_inv (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    oddPerm g⁻¹ (actWord g w) = (oddPerm g w)⁻¹ := by
  have hh := oddPerm_mul g⁻¹ g w
  rw [inv_mul_cancel, oddPerm_one] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma signedMap_transport_apply (g : Equiv.Perm S)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) (w : Words (S := S) odd k) :
    representation g x (actWord g w) = permSign (oddPerm g w) * x w := by
  change permSign (oddPerm g⁻¹ (actWord g w)) * x (actWord g⁻¹ (actWord g w)) = _
  rw [oddPerm_inv, permSign_inv, ← actWord_mul, inv_mul_cancel, actWord_one]

omit [DecidableEq S] [Fintype C] in
lemma signedMap_wordVector (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    representation g (wordVector w) = permSign (oddPerm g w) • wordVector (actWord g w) := by
  ext z
  obtain ⟨v, rfl⟩ := (wordsEquiv g).surjective z
  change representation g (wordVector w) (actWord g v) = _
  rw [signedMap_transport_apply]
  change permSign (oddPerm g v) * (if v = w then (1 : ℂ) else 0) =
    permSign (oddPerm g w) * (if actWord g v = actWord g w then (1 : ℂ) else 0)
  have he : actWord g v = actWord g w ↔ v = w := (wordsEquiv g).apply_eq_iff_eq
  simp only [he]
  by_cases hv : v = w
  · subst v; rfl
  · simp [hv]

lemma permSign_ne_zero (g : Equiv.Perm S) : permSign g ≠ 0 := by
  intro he
  have H := permSign_sq g
  rw [he, zero_mul] at H
  exact zero_ne_one H

lemma sum_wordVectors (x : EuclideanSpace ℂ (Words (S := S) odd k)) :
    (∑ w, x w • wordVector w) = x := by
  ext z
  simp [WithLp.ofLp_sum, wordVector, WithLp.ofLp_smul]

variable {L : Type*} [Fintype L] [DecidableEq L] (line : S → L)

omit [Fintype L] [DecidableEq L] [DecidableEq S] [Fintype C] in
lemma commuting_coefficient_relation
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (g : RowColumn.lineGroup line) (w v : Words (S := S) odd k) :
    permSign (oddPerm g.1 v) * T (wordVector (actWord g.1 v)) (actWord g.1 w) =
    permSign (oddPerm g.1 w) * T (wordVector v) w := by
  have he := congrArg (fun x : EuclideanSpace ℂ (Words (S := S) odd k) => x (actWord g.1 w))
    (Representation.IntertwiningMap.isIntertwining _ _ T g (wordVector v))
  change T (representation g.1 (wordVector v)) (actWord g.1 w) =
    representation g.1 (T (wordVector v)) (actWord g.1 w) at he
  rw [signedMap_wordVector, map_smul, signedMap_transport_apply] at he
  exact he

end RowColumn.Signed

namespace RowColumn.WordOrbits

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

/-- The label can record a row or a column. Joint counts then give a
word transporter inside the actual line subgroup, not an abstract action. -/
lemma line_pair_transporter {L C : Type*} [Fintype L] [Fintype C]
    [DecidableEq L] [DecidableEq C]
    (line : S → L) (w v w' v' : S → C)
    (he : counts (fun x => (line x, w x, v x)) = counts (fun x => (line x, w' x, v' x))) :
    ∃ p : Equiv.Perm S, (∀ x, line (p x) = line x) ∧
      (∀ x, w' (p x) = w x) ∧ (∀ x, v' (p x) = v x) := by
  obtain ⟨p, hp⟩ := same_counts_permutation _ _ he
  refine ⟨p, (fun x => congrArg Prod.fst (hp x)), ?_⟩
  exact ⟨(fun x => congrArg (fun z => z.2.1) (hp x)),
    (fun x => congrArg (fun z => z.2.2) (hp x))⟩

end RowColumn.WordOrbits

namespace RowColumn.Signed
open CubeShuffle.Specht
open scoped BigOperators Classical

variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}
  (line : S → L)

lemma commutantData_zero
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (hz : commutantData line T = 0) : T = 0 := by
  have hT (v : Words (S := S) odd k) : T (wordVector v) = 0 := by
    ext w
    let a := pairCounts line (w, v)
    have ha : ∃ wv, pairCounts (odd := odd) (k := k) line wv = a := ⟨(w, v), rfl⟩
    let p := Classical.choose ha
    have hp : pairCounts line p = a := Classical.choose_spec ha
    have hrep : T (wordVector p.2) p.1 = 0 := by
      have hh := congrArg (fun z : PairCountIndex (S := S) (C := C) (L := L) → ℂ => z a) hz
      simpa only [commutantData, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left ha, Pi.zero_apply]
        using hh
    obtain ⟨g, hl, hw, hv⟩ := RowColumn.WordOrbits.line_pair_transporter line
      w.1 v.1 p.1.1 p.2.1 hp.symm
    have hgw : actWord g w = p.1 := by
      apply Subtype.ext
      funext x
      have hh := hw (g⁻¹ x)
      simpa using hh.symm
    have hgv : actWord g v = p.2 := by
      apply Subtype.ext
      funext x
      have hh := hv (g⁻¹ x)
      simpa using hh.symm
    have hre := commuting_coefficient_relation line T ⟨g, hl⟩ w v
    rw [hgw, hgv, hrep, mul_zero] at hre
    exact (mul_eq_zero.mp hre.symm).resolve_left (permSign_ne_zero _)
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change T x = 0
  rw [← sum_wordVectors x, map_sum]
  simp only [map_smul, hT, smul_zero, Finset.sum_const_zero]

lemma commutantData_injective : Function.Injective
    (commutantData (odd := odd) (k := k) line) := by
  intro T U he
  apply sub_eq_zero.mp
  apply commutantData_zero line
  rw [map_sub, he, sub_self]

/-- Polynomial local multiplicity infrastructure, proved directly from
simultaneous signed-word orbits. This avoids assuming any LR-count estimate.
For the occupied board C has 2h colors, giving exponent 4*|lines|*h². -/
theorem commutant_dimension_bound :
    Module.finrank ℂ
      (Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
        (lineRepresentation (odd := odd) (k := k) line)) ≤
      (Fintype.card S + 1) ^ (Fintype.card L * Fintype.card C ^ 2) := by
  have hf := LinearMap.finrank_le_finrank_of_injective
    (f := commutantData (odd := odd) (k := k) line) (commutantData_injective line)
  simpa only [Module.finrank_fintype_fun_eq_card, PairCountIndex, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_prod, pow_two] using hf

end RowColumn.Signed

end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_HookModel
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn.HookModel
open scoped BigOperators Classical
open CubeShuffle.Specht RowColumn.Signed

variable (μ : YoungDiagram) (h : ℕ) (H : RowColumn.InHook μ h)

lemma template_parity (x : Cell μ) : IsOdd (template μ h H x) ↔ h ≤ row x := by
  unfold template
  split_ifs <;> simp_all [IsOdd]
  omega

lemma template_row {x y : Cell μ} (he : template μ h H x = template μ h H y)
    (hx : row x < h) : row x = row y := by
  by_cases hy : row y < h
  · simp only [template, dite_eq_left hx, dite_eq_left hy] at he
    exact congrArg Fin.val (Sum.inl.inj he)
  · simp only [template, dite_eq_left hx, dite_eq_right hy] at he
    cases he

lemma template_col {x y : Cell μ} (he : template μ h H x = template μ h H y)
    (hx : h ≤ row x) : col x = col y := by
  have hn : ¬ row x < h := by omega
  by_cases hy : row y < h
  · simp only [template, dite_eq_right hn, dite_eq_left hy] at he
    cases he
  · simp only [template, dite_eq_right hn, dite_eq_right hy] at he
    exact congrArg Fin.val (Sum.inr.inj he)

lemma row_preserved (r : CubeShuffle.Specht.rowGroup μ) (x : Cell μ) : row (r.1 x) = row x :=
  congrArg Fin.val (r.2 x)

/-- The nonzero coefficient of the Young symmetrizer is protected from sign
cancellation: surviving row motions fix bottom cells, and column motions fix
all top cells. -/
lemma template_rigidity (c : colGroup μ) (r : CubeShuffle.Specht.rowGroup μ)
    (hw : actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H) :
    (∀ x : Cell μ, row x < h → c.1 x = x) ∧
    (∀ x : Cell μ, h ≤ row x → r.1 x = x) := by
  have ht (x : Cell μ) : template μ h H (c.1 (r.1 x)) = template μ h H x :=
    word_stabilizer_eq _ _ hw x
  constructor
  · intro y hy
    let x := r.1⁻¹ y
    have hr : r.1 x = y := r.1.apply_symm_apply y
    have hx : row x < h := by
      have hh := row_preserved μ r x
      rw [hr] at hh
      omega
    apply Subtype.ext
    apply Prod.ext
    · change row (c.1 y) = row y
      have he := template_row μ h H (ht x).symm hx
      have hh := row_preserved μ r x
      rw [hr] at he hh
      exact he.symm.trans hh.symm
    · exact c.2 y
  · intro x hx
    apply Subtype.ext
    apply Prod.ext
    · exact row_preserved μ r x
    · change col (r.1 x) = col x
      have he := template_col μ h H (ht x).symm hx
      exact (c.2 (r.1 x)).symm.trans he.symm

lemma template_row_stabilized (r : CubeShuffle.Specht.rowGroup μ)
    (hr : ∀ x : Cell μ, h ≤ row x → r.1 x = x) :
    actWord r.1 (templateWord μ h H) = templateWord μ h H := by
  apply Subtype.ext
  funext x
  change template μ h H (r.1⁻¹ x) = template μ h H x
  have he : row (r.1⁻¹ x) = row x := row_preserved μ r⁻¹ x
  by_cases hx : row x < h
  · have hy : row (r.1⁻¹ x) < h := by omega
    simp only [template, dite_eq_left hx, dite_eq_left hy]
    exact congrArg Sum.inl (Fin.ext he)
  · have hy : h ≤ row (r.1⁻¹ x) := by omega
    have hh := hr (r.1⁻¹ x) hy
    simpa using congrArg (template μ h H) hh.symm

lemma template_young_sign (c : colGroup μ) (r : CubeShuffle.Specht.rowGroup μ)
    (hw : actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H) :
    permSign c.1 * permSign (oddPerm (c.1 * r.1) (templateWord μ h H)) = 1 := by
  obtain ⟨hc, hr⟩ := template_rigidity μ h H c r hw
  have hrw := template_row_stabilized μ h H r hr
  have hcw : actWord c.1 (templateWord μ h H) = templateWord μ h H := by
    rwa [actWord_mul, hrw] at hw
  have hro : oddPerm r.1 (templateWord μ h H) = 1 := by
    apply oddPerm_of_odd_fixed _ _ hrw
    intro x hx
    exact hr x ((template_parity μ h H x).mp hx)
  have hco : permSign (oddPerm c.1 (templateWord μ h H)) = permSign c.1 := by
    apply oddPerm_sign_of_stabilizes _ _ hcw
    intro x hx
    apply hc x
    have hh : ¬ h ≤ row x := fun he => hx ((template_parity μ h H x).mpr he)
    omega
  rw [oddPerm_mul, hrw, hro, mul_one, hco]
  exact permSign_sq c.1

end RowColumn.HookModel

namespace RowColumn
open CubeShuffle.Specht

section YoungMap
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (μ : YoungDiagram) (ρ : Representation ℂ (Equiv.Perm (Cell μ)) V) (v : V)

lemma tabloidOrbitMap_delta_base :
    tabloidOrbitMap μ ρ v (delta (baseTabloid μ)) = symmetrizer (CubeShuffle.Specht.rowGroup μ) ρ v := by
  have hmem (g : Equiv.Perm (Cell μ)) :
      tabloidAct g (baseTabloid μ) = baseTabloid μ ↔ g ∈ CubeShuffle.Specht.rowGroup μ := by
    rw [← tabloid_stabilizer]
    rfl
  change (∑ g : Equiv.Perm (Cell μ),
    (if tabloidAct g (baseTabloid μ) = baseTabloid μ then (1 : ℂ) else 0) • ρ g v) = _
  simp only [hmem, ite_smul, one_smul, zero_smul]
  simp only [symmetrizer, LinearMap.sum_apply]
  change _ = ∑ g : CubeShuffle.Specht.rowGroup μ, ρ g.1 v
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro g; simp) (fun g => ρ g v)

lemma tabloidOrbitMap_polytabloid :
    tabloidOrbitMap μ ρ v (polytabloid μ) =
      alternator (colGroup μ) ρ (symmetrizer (CubeShuffle.Specht.rowGroup μ) ρ v) := by
  rw [polytabloid_formula, map_sum]
  simp only [map_smul, alternator, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [← tabloidRep_delta, tabloidOrbitMap_intertwines, tabloidOrbitMap_delta_base]

/-- A nonvanishing actual column-alternator/row-symmetrizer vector supplies an
embedding; no Littlewood--Richardson occurrence statement is assumed. -/
theorem youngIntertwiner_injective
    (hn : alternator (colGroup μ) ρ (symmetrizer (CubeShuffle.Specht.rowGroup μ) ρ v) ≠ 0) :
    Function.Injective (youngIntertwiner μ ρ v) := by
  let := representation_irreducible μ
  rcases Representation.IsIrreducible.injective_or_eq_zero (youngIntertwiner μ ρ v) with hi | hz
  · exact hi
  · exfalso
    apply hn
    have he := congrArg (fun F : Representation.IntertwiningMap (CubeShuffle.Specht.representation μ) ρ =>
      F ⟨polytabloid μ, polytabloid_mem_space μ⟩) hz
    change tabloidOrbitMap μ ρ v (polytabloid μ) = 0 at he
    rwa [tabloidOrbitMap_polytabloid] at he

end YoungMap
end RowColumn

namespace RowColumn.HookModel
open scoped BigOperators Classical
open CubeShuffle.Specht RowColumn.Signed

variable (μ : YoungDiagram) (h : ℕ) (H : RowColumn.InHook μ h)

lemma youngVector_coefficient : youngVector μ h H (templateWord μ h H) =
    ∑ c : colGroup μ, ∑ r : CubeShuffle.Specht.rowGroup μ,
      if actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H then (1 : ℂ) else 0 := by
  unfold youngVector
  simp only [alternator, symmetrizer, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro r _
  change permSign c.1 * ((hookRepresentation μ h H c.1 * hookRepresentation μ h H r.1)
    (wordVector (templateWord μ h H))) (templateWord μ h H) = _
  rw [← map_mul]
  change permSign c.1 * Signed.representation (c.1 * r.1)
    (wordVector (templateWord μ h H)) (templateWord μ h H) = _
  rw [wordVector_coefficient]
  split_ifs with he
  · exact template_young_sign μ h H c r he
  · exact mul_zero _

lemma youngVector_nonzero : youngVector μ h H ≠ 0 := by
  have he : (youngVector μ h H (templateWord μ h H)).re =
      ∑ c : colGroup μ, ∑ r : CubeShuffle.Specht.rowGroup μ,
      if actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H then (1 : ℝ) else 0 := by
    rw [youngVector_coefficient]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> rfl
  have hp : 0 < ∑ c : colGroup μ, ∑ r : CubeShuffle.Specht.rowGroup μ,
      if actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H then (1 : ℝ) else 0 := by
    apply Finset.sum_pos'
    · intro c _
      exact Finset.sum_nonneg (fun r _ => by split_ifs <;> norm_num)
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos'
      · intro r _
        split_ifs <;> norm_num
      · refine ⟨1, Finset.mem_univ _, ?_⟩
        simp
  intro hz
  rw [hz] at he
  change 0 = _ at he
  linarith

theorem hookEmbedding_injective : Function.Injective (hookEmbedding μ h H) :=
  RowColumn.youngIntertwiner_injective μ (hookRepresentation μ h H)
    (wordVector (templateWord μ h H)) (youngVector_nonzero μ h H)

end RowColumn.HookModel

end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Multiplicity
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn

section Retraction
variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Averaging an algebraic left inverse produces a genuine equivariant retraction.
Used to transfer the signed-slot commutant bound to the hook Specht module. -/
lemma intertwiner_has_retraction (L : Representation.IntertwiningMap ρ σ)
    (hL : Function.Injective L) :
    ∃ R : Representation.IntertwiningMap σ ρ, ∀ v, R (L v) = v := by
  obtain ⟨A, hA⟩ := L.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hL)
  refine ⟨(Fintype.card G : ℂ)⁻¹ • algebraicAverage A, ?_⟩
  intro v
  change (Fintype.card G : ℂ)⁻¹ • (∑ g, (ρ g).comp (A.comp (σ g⁻¹))) (L v) = v
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  have ha (g : G) : ρ g (A (σ g⁻¹ (L v))) = v := by
    rw [← Representation.IntertwiningMap.isIntertwining ρ σ L]
    have he : A (L (ρ g⁻¹ v)) = ρ g⁻¹ v :=
      LinearMap.congr_fun hA (ρ g⁻¹ v)
    rw [he]
    change (ρ g * ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  simp only [ha, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

omit [Fintype G] in
lemma extendCommutant_injective (L : Representation.IntertwiningMap ρ σ)
    (R : Representation.IntertwiningMap σ ρ) (hL : Function.Injective L)
    (hR : ∀ v, R (L v) = v) : Function.Injective (extendCommutant L R) := by
  intro A B h
  apply Representation.IntertwiningMap.ext
  ext v
  change A v = B v
  apply hL
  have he := congrArg (fun T : Representation.IntertwiningMap σ σ => T (L v)) h
  simpa only [extendCommutant, LinearMap.coe_mk, AddHom.coe_mk,
    Representation.IntertwiningMap.comp_apply, hR] using he

lemma commutant_finrank_le_of_embedding [FiniteDimensional ℂ W]
    (L : Representation.IntertwiningMap ρ σ) (hL : Function.Injective L) :
    Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) ≤
      Module.finrank ℂ (Representation.IntertwiningMap σ σ) := by
  obtain ⟨R, hR⟩ := intertwiner_has_retraction L hL
  exact LinearMap.finrank_le_finrank_of_injective (f := extendCommutant L R)
    (extendCommutant_injective L R hL hR)

end Retraction
end RowColumn
namespace RowColumn
open scoped BigOperators Classical
open CubeShuffle.UnitaryFinite

section CopyCount
variable {G V X : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G X}
  {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] X)

lemma adjoint_copy_apply (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0)
    (i j : Fin u) (v : V) :
    (I i).toContinuousLinearMap.adjoint (I j v) = if i = j then v else 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  by_cases he : i = j
  · subst j
    simp [LinearIsometry.inner_map_map]
  · simp only [ite_eq_right he, inner_zero_right, LinearIsometry.coe_toContinuousLinearMap]
    exact ho i j he w v

lemma copyIdempotent_apply (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0)
    (i j : Fin u) (v : V) :
    copyIdempotent I hI hρ hτ i (I j v) = if i = j then I j v else 0 := by
  change I i ((I i).toContinuousLinearMap.adjoint (I j v)) = _
  rw [adjoint_copy_apply I ho]
  split_ifs with he
  · subst j; rfl
  · exact map_zero _

/-- Orthogonal nonzero copies supply linearly independent elements of the
commutant by their actual range projections. -/
lemma copyIdempotent_independent [Nontrivial V]
    (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0) :
    LinearIndependent ℂ (copyIdempotent I hI hρ hτ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  rw [linearIndependent_iff']
  intro s z hz j hj
  have he := congrArg (fun T : Representation.IntertwiningMap τ τ => T (I j v)) hz
  simp only [Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply,
    copyIdempotent_apply I hI hρ hτ ho] at he
  have he' : ∑ i ∈ s, z i • (if i = j then I j v else 0) = 0 := he
  simp only [smul_ite, smul_zero] at he'
  simp only [Finset.sum_ite_eq', ite_eq_left hj] at he'
  exact (smul_eq_zero.mp he').resolve_right (fun hz => hv ((I j).injective (hz.trans (map_zero _).symm)))

lemma copy_count_le_commutant [Nontrivial V]
    (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0) :
    u ≤ Module.finrank ℂ (Representation.IntertwiningMap τ τ) := by
  simpa using (copyIdempotent_independent I hI hρ hτ ho).fintype_card_le_finrank
end CopyCount
end RowColumn
namespace RowColumn
open scoped BigOperators Classical
open CubeShuffle.Specht CubeShuffle.UnitaryFinite

section Transfer
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

lemma commutantOfComp_injective (ρ : Representation ℂ G V) (e : H ≃* G) :
    Function.Injective (commutantOfComp ρ e) := by
  intro T U he
  exact Representation.IntertwiningMap.ext
    (congrArg (fun T : Representation.IntertwiningMap ρ ρ => T.toLinearMap) he)

lemma commutant_comp_finrank_le [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (e : H ≃* G) :
    Module.finrank ℂ (Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) ≤
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) :=
  LinearMap.finrank_le_finrank_of_injective (commutantOfComp_injective ρ e)
end Transfer

section HookMultiplicity
variable {S L : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  (f : S → L) (a : YoungDiagram) (e : S ≃ Cell a) (h : ℕ) (H : InHook a h)

omit [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L] in
lemma hookLineEmbedding_injective : Function.Injective (hookLineEmbedding f a e h H) :=
  (HookModel.hookEmbedding_injective a h H).comp (spaceHilbertEquiv a).symm.injective

include H

/-- Polynomial commutant estimate for the actual hook Specht representation
restricted to arbitrary fibres. This is the required first multiplicity bound
for both row and column restrictions in the occupied theorem. -/
lemma hook_line_commutant_bound :
    Module.finrank ℂ (Representation.IntertwiningMap
      ((relabelledUnitary a e).comp (lineGroup f).subtype)
      ((relabelledUnitary a e).comp (lineGroup f).subtype)) ≤
      (Fintype.card S + 1) ^ (4 * Fintype.card L * h ^ 2) := by
  apply (commutant_finrank_le_of_embedding (hookLineEmbedding f a e h H)
    (hookLineEmbedding_injective f a e h H)).trans
  apply (commutant_comp_finrank_le _ (lineGroupCongr e f)).trans
  have hc := Signed.commutant_dimension_bound (odd := HookModel.IsOdd (h := h))
    (k := HookModel.oddCount a h H) (f ∘ e.symm)
  have hs : Fintype.card (Cell a) = Fintype.card S := (Fintype.card_congr e).symm
  simpa only [hs, HookModel.Color, Fintype.card_sum, Fintype.card_fin,
    show Fintype.card L * (h + h) ^ 2 = 4 * Fintype.card L * h ^ 2 by ring] using hc

lemma hook_line_copy_count {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ (lineGroup f) V)
    (hρ : IsUnitary ρ) {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] hilbertSpace a)
    (hI : CompleteCopies (V := V) (W := hilbertSpace a) ρ ((relabelledUnitary a e).comp (lineGroup f).subtype) I) :
    u ≤ (Fintype.card S + 1) ^ (4 * Fintype.card L * h ^ 2) :=
  (copy_count_le_commutant (V := V) (X := hilbertSpace a) I hI.1 hρ (fun g => relabelledUnitary_unitary a e g.1) hI.2.1).trans
    (hook_line_commutant_bound f a e h H)

end HookMultiplicity
end RowColumn

end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_CopyOverlap
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace RowColumn
open CubeShuffle.UnitaryFinite
variable {V W X E G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {u v : ℕ}

lemma allCopyOverlap_le_count (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) : allCopyOverlap I J ≤ (u : ℝ) * v := by
  unfold allCopyOverlap
  have h (i : Fin u) (j : Fin v) :
      ‖(I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap‖^2 ≤ 1 := by
    have hn := ContinuousLinearMap.opNorm_comp_le (I i).toContinuousLinearMap.adjoint
      (J j).toContinuousLinearMap
    rw [ContinuousLinearMap.adjoint.norm_map] at hn
    have hb := mul_le_mul (I i).norm_toContinuousLinearMap_le (J j).norm_toContinuousLinearMap_le
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have hz : ‖(I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap‖ ≤ 1 :=
      hn.trans (by simpa using hb)
    nlinarith [norm_nonneg ((I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap)]
  calc
    _ ≤ ∑ _i : Fin u, ∑ _j : Fin v, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by simp

end RowColumn

end
end


end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Occupied
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn

/-- Absorption of the exact polynomial loss into the absolute occupied-board
constant. This is used for both halves of the min. -/
lemma occupied_numeric_absorb (m n h s : ℕ) (hh : 1 ≤ h) (hs : s ≤ m*n) :
    16 * ((s : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp ((m*n-s : ℕ) : ℝ) ≤
      Real.exp (128 * (((m+n+1 : ℕ) : ℝ)*(h : ℝ)^2 * Real.log ((m*n : ℕ)+2) +
        (m*n-s : ℕ))) := by
  let N : ℝ := (m*n : ℕ)+2
  let E : ℕ := (16*(m+n)+8)*h^2
  have hN : 2 ≤ N := by dsimp [N]; have := (Nat.cast_nonneg (m*n) : (0 : ℝ) ≤ (m*n : ℕ)); linarith
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hb : 0 ≤ (s : ℝ)+1 := by positivity
  have hbs : (s : ℝ)+1 ≤ N := by dsimp [N]; exact_mod_cast (by omega : s+1 ≤ m*n+2)
  have h16 : (16 : ℝ) ≤ N^4 := by
    calc 16 = (2 : ℝ)^4 := by norm_num
         _ ≤ N^4 := pow_le_pow_left₀ (by norm_num) hN _
  have hp : 16 * ((s : ℝ)+1)^E ≤ N^(E+4) := by
    calc _ ≤ N^4 * N^E := mul_le_mul h16 (pow_le_pow_left₀ hb hbs _) (by positivity) (by positivity)
         _ = N^(E+4) := by rw [pow_add]; ring
  have hh2 : (1 : ℝ) ≤ (h : ℝ)^2 := by exact_mod_cast (Nat.one_le_pow 2 h hh)
  have he : ((E+4 : ℕ) : ℝ) ≤ 128*((m+n+1 : ℕ) : ℝ)*(h : ℝ)^2 := by
    dsimp [E]
    push_cast
    nlinarith [sq_nonneg (h : ℝ), mul_nonneg (show 0 ≤ (m:ℝ)+(n:ℝ) by positivity) (sq_nonneg (h:ℝ))]
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have ht : (0 : ℝ) ≤ (m*n-s : ℕ) := Nat.cast_nonneg _
  have hexp : N^(E+4) = Real.exp (((E+4 : ℕ) : ℝ)*Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hNp]
  change 16 * ((s : ℝ)+1)^E * Real.exp ((m*n-s : ℕ) : ℝ) ≤ _
  calc
    _ ≤ N^(E+4) * Real.exp ((m*n-s : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (((E+4 : ℕ) : ℝ)*Real.log N + (m*n-s : ℕ)) := by rw [hexp, Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      change ((E+4 : ℕ) : ℝ)*Real.log N + (m*n-s : ℕ) ≤
        128 * (((m+n+1 : ℕ) : ℝ)*(h : ℝ)^2 * Real.log N + (m*n-s : ℕ))
      nlinarith [mul_le_mul_of_nonneg_right he hl]

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn

lemma occupied_count_bound (s m n h u v : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hu : u ≤ (s+1)^(4*m*h^2)) (hv : v ≤ (s+1)^(4*n*h^2)) :
    (u : ℝ)*v ≤ 16 * ((s : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp t := by
  have huv : (u : ℝ)*v ≤ ((s : ℝ)+1)^(4*(m+n)*h^2) := by
    have hu' : (u : ℝ) ≤ ((s : ℝ)+1)^(4*m*h^2) := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ ((s : ℝ)+1)^(4*n*h^2) := by exact_mod_cast hv
    calc _ ≤ ((s : ℝ)+1)^(4*m*h^2) * ((s : ℝ)+1)^(4*n*h^2) :=
            mul_le_mul hu' hv' (by positivity) (by positivity)
         _ = _ := by rw [← pow_add]; congr 1; ring
  have he : 4*(m+n)*h^2 ≤ (16*(m+n)+8)*h^2 := Nat.mul_le_mul_right _ (by omega)
  have hb : 1 ≤ (s : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) s; linarith
  have hp := pow_le_pow_right₀ hb he
  have hx : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hbase : 0 ≤ ((s : ℝ)+1)^((16*(m+n)+8)*h^2) := by positivity
  calc _ ≤ ((s : ℝ)+1)^((16*(m+n)+8)*h^2) := huv.trans hp
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hx hbase]

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.Specht Signed MatrixState

lemma irreducible_nontrivial {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] : Nontrivial V := by
  let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  exact ρ.asModuleEquiv.symm.toEquiv.nontrivial

lemma empty_hook_dimension_le (a : YoungDiagram) (h : ℕ) (H : InHook a h)
    (ha : Fintype.card (Cell a)=0) : Module.finrank ℂ (space a) ≤ 1 := by
  have hi := LinearMap.finrank_le_finrank_of_injective (HookModel.hookEmbedding_injective a h H)
  change Module.finrank ℂ (space a) ≤
    Module.finrank ℂ (EuclideanSpace ℂ (Words (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))) at hi
  rw [finrank_euclideanSpace] at hi
  calc _ ≤ Fintype.card (Words (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H)) := hi
       _ ≤ Fintype.card (Cell a → HookModel.Color h) := Fintype.card_subtype_le _
       _ = 1 := by rw [Fintype.card_fun, ha, pow_zero]

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState

/-- `thm:occupied` (weighted.tex:76–84), including the empty occupied subset,
arbitrary deletion layout and every orthogonal multiplicity copy. The absolute
constant is 128; dimensions, unnormalized trace and operator norm are literal. -/
theorem occupied_overlap_endpoint_oai : OccupiedOverlapEndpoint := by
  refine ⟨128, by norm_num, ?_⟩
  intro m n Ω a e h hh hN H r c u v ρ τ hirρ hirτ hρ hτ I J hI hJ
  let : Representation.IsIrreducible ρ := hirρ
  let : Representation.IsIrreducible τ := hirτ
  let : Nontrivial (EuclideanSpace ℂ (Fin r)) := irreducible_nontrivial ρ
  let : Nontrivial (EuclideanSpace ℂ (Fin c)) := irreducible_nontrivial τ

  have hu : u ≤ (Ω.card+1)^(4*m*h^2) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      hook_line_copy_count (V := EuclideanSpace ℂ (Fin r)) (fun x : Ω => x.1.1) a e h H ρ hρ I hI
  have hv : v ≤ (Ω.card+1)^(4*n*h^2) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      hook_line_copy_count (V := EuclideanSpace ℂ (Fin c)) (fun x : Ω => x.1.2) a e h H τ hτ J hJ

  let loss : ℝ := 16 * ((Ω.card : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp ((m*n-Ω.card : ℕ) : ℝ)
  let ratio : ℝ := (r : ℝ)*c / Module.finrank ℂ (space a)
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity

  have hplain : allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤ loss :=
    (@allCopyOverlap_le_count (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin c))
      (hilbertSpace a) inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance u v I J).trans
      (occupied_count_bound Ω.card m n h u v ((m*n-Ω.card : ℕ) : ℝ) (Nat.cast_nonneg _) hu hv)

  have hdim : allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤ loss * ratio := by
    by_cases hΩ : Ω.Nonempty
    · obtain ⟨x,hx⟩ := hΩ
      let : Nonempty Ω := ⟨⟨x,hx⟩⟩
      exact occupied_dimension_ratio m n Ω a e h hh H r c u v ρ τ hρ hτ I J hI.1 hJ.1 hu hv
    · have hempty : Ω=∅ := Finset.not_nonempty_iff_eq_empty.mp hΩ
      have ha : Fintype.card (Cell a)=0 := by
        rw [← Fintype.card_congr e, Fintype.card_coe, hempty, Finset.card_empty]
      have hd : (Module.finrank ℂ (space a) : ℝ) ≤ 1 := by exact_mod_cast empty_hook_dimension_le a h H ha
      have hdpos : (0 : ℝ) < Module.finrank ℂ (space a) := by exact_mod_cast dimension_pos a
      have hr : (1 : ℝ) ≤ r := by
        have hh : 0 < Module.finrank ℂ (EuclideanSpace ℂ (Fin r)) := Module.finrank_pos
        simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
        exact_mod_cast hh
      have hc : (1 : ℝ) ≤ c := by
        have hh : 0 < Module.finrank ℂ (EuclideanSpace ℂ (Fin c)) := Module.finrank_pos
        simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
        exact_mod_cast hh
      have hrc : 1 ≤ ratio := by
        dsimp [ratio]
        apply (le_div_iff₀ hdpos).mpr
        simp only [one_mul]
        exact hd.trans (one_le_mul_of_one_le_of_one_le hr hc)
      exact hplain.trans (by simpa using mul_le_mul_of_nonneg_left hrc hloss)

  have hmin : allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤ loss * min 1 ratio := by
    by_cases hx : ratio ≤ 1
    · rw [min_eq_right hx]; exact hdim
    · rw [min_eq_left (le_of_not_ge hx), mul_one]; exact hplain

  have hs : Ω.card ≤ m*n := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Finset.card_le_univ Ω
  have hbound := occupied_numeric_absorb m n h Ω.card hh hs

  exact hmin.trans (mul_le_mul_of_nonneg_right hbound (le_min (by norm_num) hratio))

end RowColumn

end
end

end OAI
end

theorem solution : type_of% @OAI.RowColumn.occupied_overlap_endpoint_oai := @OAI.RowColumn.occupied_overlap_endpoint_oai
