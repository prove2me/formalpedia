-- Prove2me | solution 1 for OAI.ThorpNine.Adaptive.Thorp.Specht.spectral_regimes_q77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:03:13.393991+00:00
-- url     : https://prove2.me/submissions/95ebcf42-045f-4bb5-a5f8-2b70755b341f

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000
import Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_Specht_exponential_dimension_spectral_q77
import Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_Specht_near_row_amplification_q77

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_Coins
attribute [-instance] _root_.OAI.ThorpNine.Adaptive.Thorp.instFintypeSelectedCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

open scoped BigOperators
open Filter

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_HeightDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

lemma heightDecay_nonneg (H : ℕ) : 0 ≤ heightDecay H := by
  have h : Real.exp (-(1:ℝ)/64) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  apply div_nonneg (by positivity) (by linarith)

lemma densityTailConstant_nonneg : 0 ≤ densityTailConstant := by
  have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
  apply div_nonneg (by positivity) (by linarith)

lemma densityConstant_pos : 0 < densityConstant := by
  dsimp [densityConstant]
  have hh := heightDecay_nonneg 1
  have ht := densityTailConstant_nonneg
  linarith

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedReverseEquiv
attribute [-instance] _root_.OAI.ThorpNine.Adaptive.Thorp.Specht.tabloidMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.Specht
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


lemma permSign_sq {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    permSign p * permSign p = 1 := by
  calc
    permSign p * permSign p = permSign (p*p⁻¹) := by rw [permSign_mul,permSign_inv]
    _ = 1 := by simp

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

end Thorp.Specht
namespace Thorp.Specht
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

lemma delta_decomposition {μ : YoungDiagram} (v : Tabloid μ → ℂ) :
    v = ∑ f : Tabloid μ, v f • delta f := by
  classical
  funext g
  simp only [Finset.sum_apply,Pi.smul_apply,delta,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp

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

lemma alternator_base_pairing (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v (baseTabloid μ) = pairing (polytabloid μ) v := by
  classical
  simp only [polytabloid_formula,pairing_sum_left,pairing_smul_left,conj_permSign,pairing_delta]
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,tabloidRep_apply]
  apply Fintype.sum_equiv (Equiv.inv (colGroup μ))
  intro c
  simp only [Equiv.inv_apply,Subgroup.coe_inv,permSign_inv]

theorem alternator_pairing (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v = pairing (polytabloid μ) v • polytabloid μ := by
  rw [alternator_rank_one_exact,alternator_base_pairing]


lemma polytabloid_mem_space (μ : YoungDiagram) : polytabloid μ ∈ space μ := by
  simpa using orbit_mem_space μ 1

end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ShapePartitionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.PermutationHilbert

section
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

end
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

lemma trace_projection_real (W : Submodule ℂ (H X)) :
    ∑ x, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 = (Module.finrank ℂ W:ℝ) := by
  have hh := trace_projection W
  simp_rw [projection_diagonal] at hh
  exact_mod_cast hh

theorem footprint_dimension (W K : Submodule ℂ (H X)) (hKW : K ≤ W)
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (S : Finset X) (hS : ∀ x ∈ S, W.starProjection (EuclideanSpace.single x (1:ℂ)) ∈ K) :
    (S.card:ℝ) * (Module.finrank ℂ W:ℝ) ≤
      (Fintype.card X:ℝ) * (Module.finrank ℂ K:ℝ) := by
  have he (x : X) (hx : x ∈ S) :
      K.starProjection (EuclideanSpace.single x (1:ℂ)) =
        W.starProjection (EuclideanSpace.single x (1:ℂ)) := by
    apply K.eq_starProjection_of_mem_of_inner_eq_zero (hS x hx)
    intro v hv
    exact W.starProjection_inner_eq_zero _ v (hKW hv)
  have hs : ∑ x ∈ S, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 ≤
      (Module.finrank ℂ K:ℝ) := by
    rw [←trace_projection_real K]
    calc
      _ = ∑ x ∈ S, ‖K.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [he x hx]
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun x => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card X): (0:ℝ) ≤ _)
  rw [Finset.mul_sum] at hmul
  simp_rw [uniform_diagonal W htrans] at hmul
  simpa using hmul

end Thorp.PermutationHilbert
namespace Thorp.Specht
open scoped BigOperators Classical

lemma finrank_hilbertSpace (μ : YoungDiagram) :
    Module.finrank ℂ (hilbertSpace μ) = Module.finrank ℂ (space μ) :=
  (hilbertEquiv μ).finrank_map_eq (space μ)

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


section FiberGroup
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma nat_card_fiberGroup (f : α → β) :
    Nat.card (fiberGroup f) = ∏ b, (Nat.card {x // f x=b}).factorial := by
  rw [Nat.card_congr (fiberGroupEquiv f),Nat.card_pi]
  simp only [Nat.card_eq_fintype_card,Fintype.card_perm]

omit [Fintype β] [Fintype γ] in

lemma card_fiberGroups_mul_le (f : α → β) (g : α → γ)
    (hinj : ∀ x y, f x = f y → g x = g y → x=y) :
    Fintype.card (fiberGroup f) * Fintype.card (fiberGroup g) ≤ (Fintype.card α).factorial := by
  have hi : Function.Injective (fun p : fiberGroup f × fiberGroup g => p.1.1*p.2.1) := by
    intro p q hpq
    dsimp only at hpq
    have he : p.1.1⁻¹*q.1.1 = p.2.1*q.2.1⁻¹ := by
      apply inv_mul_eq_iff_eq_mul.mpr
      rw [←mul_assoc,hpq,mul_assoc,mul_inv_cancel,mul_one]
    have hf : p.1.1⁻¹*q.1.1 ∈ fiberGroup f := (fiberGroup f).mul_mem ((fiberGroup f).inv_mem p.1.2) q.1.2
    have hg : p.1.1⁻¹*q.1.1 ∈ fiberGroup g := he ▸ (fiberGroup g).mul_mem p.2.2 ((fiberGroup g).inv_mem q.2.2)
    have h1 : p.1.1⁻¹*q.1.1 = 1 := by
      apply Equiv.ext
      intro x
      exact hinj _ x (hf x) (hg x)
    have hpf : p.1=q.1 := Subtype.ext (inv_mul_eq_one.mp h1)
    have hpg : p.2=q.2 := by
      apply Subtype.ext
      have hh := hpq
      rw [show p.1.1=q.1.1 from congrArg Subtype.val hpf] at hh
      exact mul_left_cancel hh
    exact Prod.ext hpf hpg
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_prod,Fintype.card_perm] using hc

end FiberGroup

lemma colGroup_eq (μ : YoungDiagram) : colGroup μ = fiberGroup (colIndex (μ := μ)) := by
  ext p
  constructor
  · intro hp x; exact Fin.ext (hp x)
  · intro hp x; exact congrArg Fin.val (hp x)

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

theorem factorial_le_dimension_row_column (μ : YoungDiagram) :
    μ.card.factorial ≤ Module.finrank ℂ (space μ)*Fintype.card (rowGroup μ)*Fintype.card (colGroup μ) := by
  rw [←card_tabloid_mul_row]
  nlinarith [dimension_times_column_ge_tabloids μ]


lemma card_row_fiber (μ : YoungDiagram) (i : Fin (μ.colLen 0)) :
    Fintype.card {x : Cell μ // rowIndex x = i} = μ.rowLen i := by
  let e : {x : Cell μ // rowIndex x = i} ≃ {x : Cell μ // row x = i} :=
    Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
  rw [Fintype.card_congr e,Fintype.card_congr (rowEquiv μ i),Fintype.card_fin]

lemma card_col_fiber (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    Fintype.card {x : Cell μ // colIndex x = j} = μ.colLen j := by
  let e : {x : Cell μ // colIndex x = j} ≃ {x : Cell μ // col x = j} :=
    Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
  rw [Fintype.card_congr e,Fintype.card_congr (columnEquiv μ j),Fintype.card_fin]

lemma card_rowGroup (μ : YoungDiagram) :
    Fintype.card (rowGroup μ) = ∏ i : Fin (μ.colLen 0), (μ.rowLen i).factorial := by
  rw [←Nat.card_eq_fintype_card,rowGroup,nat_card_fiberGroup]
  simp only [Nat.card_eq_fintype_card]
  simp only [card_row_fiber]

lemma card_colGroup (μ : YoungDiagram) :
    Fintype.card (colGroup μ) = ∏ j : Fin (μ.rowLen 0), (μ.colLen j).factorial := by
  rw [←Nat.card_eq_fintype_card,colGroup_eq,nat_card_fiberGroup]
  simp only [Nat.card_eq_fintype_card,card_col_fiber]

lemma tail_card (μ : YoungDiagram) : Fintype.card (Tail μ) = μ.card - μ.rowLen 0 := by
  have hh := Fintype.card_subtype_compl (p := fun x : Cell μ => row x=0)
  rw [Fintype.card_congr (rowEquiv μ 0),Fintype.card_fin,card_cell] at hh
  exact hh

lemma rowLen_zero_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.card := by
  have h := Fintype.card_subtype_le (fun x : Cell μ => row x=0)
  rwa [Fintype.card_congr (rowEquiv μ 0),Fintype.card_fin,card_cell] at h

lemma card_tail_col (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    Fintype.card {x : Tail μ // colIndex x.1 = j} = μ.colLen j-1 := by
  rw [Fintype.card_congr (tailColumnEquiv μ j),Fintype.card_fin]

lemma card_tail_row (μ : YoungDiagram) (i : Fin (μ.colLen 0)) :
    Fintype.card {x : Tail μ // rowIndex x.1 = i} = if i.val=0 then 0 else μ.rowLen i := by
  by_cases hi : i.val=0
  · rw [ite_eq_left hi]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun x => x.1.2 ?_⟩
    exact (congrArg Fin.val x.2).trans hi
  · rw [ite_eq_right hi]
    let e : {x : Tail μ // rowIndex x.1 = i} ≃ {x : Cell μ // rowIndex x=i} :=
      { toFun := fun x => ⟨x.1.1,x.2⟩
        invFun := fun x => ⟨⟨x.1,fun hz => hi ((congrArg Fin.val x.2).symm.trans hz)⟩,x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Fintype.card_congr e,card_row_fiber]

lemma tail_row_group (μ : YoungDiagram) :
    (μ.rowLen 0).factorial * Fintype.card (fiberGroup (fun x : Tail μ => rowIndex x.1)) =
      Fintype.card (rowGroup μ) := by
  rw [←Nat.card_eq_fintype_card (α := fiberGroup (fun x : Tail μ => rowIndex x.1)),nat_card_fiberGroup,card_rowGroup]
  simp only [Nat.card_eq_fintype_card]
  simp only [card_tail_row]
  by_cases hn : μ.colLen 0=0
  · have hr : μ.rowLen 0=0 := by
      by_contra h
      have hmem : (0,0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
      have hh := YoungDiagram.mem_iff_lt_colLen.mp hmem
      omega
    let : IsEmpty (Fin (μ.colLen 0)) := ⟨fun i => by have := i.isLt; omega⟩
    simp [hr]
  · let z : Fin (μ.colLen 0) := ⟨0,Nat.pos_of_ne_zero hn⟩
    have hz : ∀ i : Fin (μ.colLen 0), i.val=0 ↔ i=z := fun i => by simp [z,Fin.ext_iff]
    simp only [hz]
    have hprod : (∏ x : Fin (μ.colLen 0), (if x=z then 0 else μ.rowLen x).factorial) =
        ∏ x ∈ Finset.univ.erase z, (μ.rowLen x).factorial := by
      rw [←Finset.prod_erase_mul Finset.univ (fun x : Fin (μ.colLen 0) => (if x=z then 0 else μ.rowLen x).factorial) (Finset.mem_univ z)]
      simp only [ite_true,Nat.factorial_zero,mul_one]
      apply Finset.prod_congr rfl
      intro x hx
      rw [ite_eq_right (Finset.mem_erase.mp hx).1]
    rw [hprod]
    exact Finset.mul_prod_erase Finset.univ (fun i : Fin (μ.colLen 0) => (μ.rowLen i).factorial) (Finset.mem_univ z)

lemma sum_tail_columns (μ : YoungDiagram) :
    ∑ j : Fin (μ.rowLen 0), (μ.colLen j-1) = μ.card-μ.rowLen 0 := by
  simp_rw [←card_tail_col]
  rw [←Fintype.card_sigma,Fintype.card_congr (Equiv.sigmaFiberEquiv (fun x : Tail μ => colIndex x.1)),tail_card]

lemma column_pos (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) : 0 < μ.colLen j :=
  YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)

lemma nat_le_two_pow_pred (n : ℕ) (hn : 0<n) : n ≤ 2^(n-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.add_one_sub_one]
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma column_group_le_tail (μ : YoungDiagram) :
    Fintype.card (colGroup μ) ≤ 2^(μ.card-μ.rowLen 0) *
      Fintype.card (fiberGroup (fun x : Tail μ => colIndex x.1)) := by
  rw [card_colGroup,←Nat.card_eq_fintype_card (α := fiberGroup (fun x : Tail μ => colIndex x.1)),nat_card_fiberGroup]
  simp only [Nat.card_eq_fintype_card]
  simp only [card_tail_col]
  calc
    _ = ∏ j : Fin (μ.rowLen 0), μ.colLen j * (μ.colLen j-1).factorial := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (Nat.mul_factorial_pred (column_pos μ j).ne').symm
    _ ≤ ∏ j : Fin (μ.rowLen 0), 2^(μ.colLen j-1) * (μ.colLen j-1).factorial := by
      apply Finset.prod_le_prod'
      intro j hj
      exact Nat.mul_le_mul_right _ (nat_le_two_pow_pred _ (column_pos μ j))
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,sum_tail_columns]

theorem choose_tail_le_dimension (μ : YoungDiagram) :
    μ.card.choose (μ.card-μ.rowLen 0) ≤ Module.finrank ℂ (space μ) * 2^(μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  have htail := card_fiberGroups_mul_le
    (fun x : Tail μ => rowIndex x.1) (fun x : Tail μ => colIndex x.1)
    (fun x y hr hc => Subtype.ext (Subtype.ext (Prod.ext (congrArg Fin.val hr) (congrArg Fin.val hc))))
  rw [tail_card] at htail
  have hc := column_group_le_tail μ
  have hr := tail_row_group μ
  have hd := factorial_le_dimension_row_column μ
  simp only [←Nat.card_eq_fintype_card] at htail hc hr hd
  have hh : μ.card.factorial ≤ Module.finrank ℂ (space μ) * 2^j *
      ((μ.rowLen 0).factorial * j.factorial) := by
    calc
      _ ≤ _ := hd
      _ ≤ Module.finrank ℂ (space μ) * Nat.card (rowGroup μ) *
          (2^j * Nat.card (fiberGroup (fun x : Tail μ => colIndex x.1))) := Nat.mul_le_mul_left _ hc
      _ = Module.finrank ℂ (space μ) * 2^j * (μ.rowLen 0).factorial *
          (Nat.card (fiberGroup (fun x : Tail μ => rowIndex x.1)) *
           Nat.card (fiberGroup (fun x : Tail μ => colIndex x.1))) := by rw [←hr]; ring
      _ ≤ _ := by
        calc
          _ ≤ Module.finrank ℂ (space μ) * 2^j * (μ.rowLen 0).factorial * j.factorial :=
            Nat.mul_le_mul_left _ htail
          _ = _ := by ring
  have hj : j ≤ μ.card := Nat.sub_le _ _
  have hs : μ.card-j = μ.rowLen 0 := by dsimp [j]; have := rowLen_zero_le_card μ; omega
  have hf := Nat.choose_mul_factorial_mul_factorial hj
  rw [hs] at hf
  rw [←hf] at hh
  have hpos : 0 < (μ.rowLen 0).factorial * j.factorial := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  nlinarith


lemma exists_perm_mem_iff {α : Type*} [Fintype α] (s t : Finset α) (hc : s.card=t.card) :
    ∃ p : Equiv.Perm α, ∀ x, p x ∈ t ↔ x ∈ s := by
  let e : s ≃ t := Finset.equivOfCardEq hc
  let ec : {x : α // x ∉ s} ≃ {x : α // x ∉ t} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_subtype_compl,Fintype.card_coe,hc])
  let p := (Equiv.sumCompl (· ∈ s)).symm.trans ((Equiv.sumCongr e ec).trans (Equiv.sumCompl (· ∈ t)))
  refine ⟨p,fun x => ?_⟩
  by_cases hx : x ∈ s
  · have hp : p x ∈ t := by
      change ((Equiv.sumCompl (· ∈ t)) ((Equiv.sumCongr e ec) ((Equiv.sumCompl (· ∈ s)).symm x))) ∈ t
      rw [Equiv.sumCompl_symm_apply_of_pos hx]
      exact (e ⟨x,hx⟩).2
    exact iff_of_true hp hx
  · have hp : p x ∉ t := by
      change ((Equiv.sumCompl (· ∈ t)) ((Equiv.sumCongr e ec) ((Equiv.sumCompl (· ∈ s)).symm x))) ∉ t
      rw [Equiv.sumCompl_symm_apply_of_neg hx]
      exact (ec ⟨x,hx⟩).2
    exact iff_of_false hp hx

lemma tailSet_act {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) (f : Tabloid μ) :
    tailSet (tabloidAct p f) = (tailSet f).image p := by
  ext x
  simp only [mem_tailSet,tabloidAct_apply,Finset.mem_image]
  constructor
  · intro h; exact ⟨p⁻¹ x,h,by simp⟩
  · rintro ⟨y,hy,rfl⟩; simpa using hy

lemma card_tailSet {μ : YoungDiagram} (f : Tabloid μ) :
    (tailSet f).card = μ.card-μ.rowLen 0 := by
  obtain ⟨p,rfl⟩ := tabloidAct_transitive μ (baseTabloid μ) f
  rw [tailSet_act,Finset.card_image_of_injective _ p.injective]
  change (Finset.univ.filter (fun x : Cell μ => row x ≠ 0)).card = _
  rw [←Fintype.card_subtype]
  exact tail_card μ

lemma tail_fiber_card_eq (μ : YoungDiagram) (s t : Finset (Cell μ)) (hst : s.card=t.card) :
    (Finset.univ.filter (fun f : Tabloid μ => tailSet f=s)).card =
      (Finset.univ.filter (fun f : Tabloid μ => tailSet f=t)).card := by
  obtain ⟨p,hp⟩ := exists_perm_mem_iff s t hst
  have he : s.image p=t := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (hp y).mpr hy
    · intro hx
      exact Finset.mem_image.mpr ⟨p⁻¹ x,(hp (p⁻¹ x)).mp (by simpa using hx),by simp⟩
  apply Finset.card_equiv (tabloidAct p)
  intro f
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,tailSet_act,←he]
  exact (Finset.image_inj p.injective).symm

lemma footprint_card_product (μ : YoungDiagram) (A : Finset (Cell μ)) :
    (footprint μ A).card * μ.card.choose (μ.card-μ.rowLen 0) =
      Fintype.card (Tabloid μ) * A.card.choose (μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  let s := tailSet (baseTabloid μ)
  let c := (Finset.univ.filter (fun f : Tabloid μ => tailSet f=s)).card
  have hconstant (t : Finset (Cell μ)) (ht : t.card=j) :
      (Finset.univ.filter (fun f : Tabloid μ => tailSet f=t)).card = c :=
    tail_fiber_card_eq μ t s (ht.trans (card_tailSet _).symm)
  have hcount (A : Finset (Cell μ)) : (footprint μ A).card = A.card.choose j*c := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Tabloid μ)) (A.powersetCard j) tailSet
    have he : (Finset.univ.filter (fun f : Tabloid μ => tailSet f ∈ A.powersetCard j)) = footprint μ A := by
      ext f
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powersetCard,
        card_tailSet,footprint]
      simp [j]
    rw [he] at h
    rw [←h]
    calc
      _ = ∑ _t ∈ A.powersetCard j, c := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hconstant t (Finset.mem_powersetCard.mp ht).2
      _ = _ := by simp [Finset.card_powersetCard]
  have hfull : (footprint μ Finset.univ).card = Fintype.card (Tabloid μ) := by
    simp only [footprint,Finset.subset_univ,Finset.filter_true,Finset.card_univ]
  have hN := hcount Finset.univ
  rw [hfull,Finset.card_univ,card_cell] at hN
  rw [hcount,hN]
  ring

lemma footprint_fixed {μ : YoungDiagram} (A : Finset (Cell μ))
    (f : Tabloid μ) (hf : f ∈ footprint μ A) (p : Equiv.Perm (Cell μ))
    (hp : ∀ x ∈ A, p x=x) : tabloidAct p f=f := by
  have htail : tailSet f ⊆ A := (Finset.mem_filter.mp hf).2
  apply Subtype.ext
  funext x
  change f.1 (p⁻¹ x) = f.1 x
  by_cases hx : x ∈ A
  · rw [show p⁻¹ x=x from p.injective (by simpa using (hp x hx).symm)]
  · have hy : p⁻¹ x ∉ A := by
      intro h
      have hh := hp (p⁻¹ x) h
      have he : x=p⁻¹ x := by simpa using hh
      exact hx (he ▸ h)
    apply Fin.ext
    have hx0 : (f.1 x).val=0 := by by_contra h; exact hx (htail (mem_tailSet f x |>.mpr h))
    have hy0 : (f.1 (p⁻¹ x)).val=0 := by by_contra h; exact hy (htail (mem_tailSet f _ |>.mpr h))
    exact hy0.trans hx0.symm

lemma fixedHilbert_le (μ : YoungDiagram) (A : Finset (Cell μ)) : fixedHilbert μ A ≤ hilbertSpace μ :=
  fun _ hv => hv.1

theorem fixedHilbert_dimension (μ : YoungDiagram) (A : Finset (Cell μ)) :
    Module.finrank ℂ (space μ) * A.card.choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (fixedHilbert μ A) * μ.card.choose (μ.card-μ.rowLen 0) := by
  let : DecidableEq (Tabloid μ) := Classical.decEq _
  have ht (f g : Tabloid μ) : ∃ p : Equiv.Perm (Tabloid μ), p f=g ∧
      (hilbertSpace μ).map (PermutationHilbert.act p).toLinearEquiv.toLinearMap = hilbertSpace μ := by
    obtain ⟨p,hp⟩ := tabloidAct_transitive μ f g
    exact ⟨tabloidAct p,hp,hilbertSpace_invariant μ p⟩
  have hproj (f : Tabloid μ) (hf : f ∈ footprint μ A) :
      (hilbertSpace μ).starProjection (EuclideanSpace.single f (1:ℂ)) ∈ fixedHilbert μ A := by
    refine ⟨((hilbertSpace μ).orthogonalProjectionOnto _).2,fun p hp => ?_⟩
    rw [PermutationHilbert.projection_comm _ _ (hilbertSpace_invariant μ p),
      PermutationHilbert.act_single,footprint_fixed A f hf p hp]
  have h := PermutationHilbert.footprint_dimension (hilbertSpace μ) (fixedHilbert μ A)
    (fixedHilbert_le μ A) ht (footprint μ A) hproj
  rw [finrank_hilbertSpace] at h
  have hn : (footprint μ A).card * Module.finrank ℂ (space μ) ≤
      Fintype.card (Tabloid μ)*Module.finrank ℂ (fixedHilbert μ A) := by exact_mod_cast h
  have hc := footprint_card_product μ A
  have hpos : 0 < Fintype.card (Tabloid μ) := Fintype.card_pos_iff.mpr ⟨baseTabloid μ⟩
  have hh := Nat.mul_le_mul_right (μ.card.choose (μ.card-μ.rowLen 0)) hn
  nlinarith

end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedStageEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.Specht
open scoped BigOperators Classical

theorem tupleFixed_dimension (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(tupleFixedEquiv μ e).finrank_eq,finrank_hilbertSpace]
  have h := fixedHilbert_dimension μ (Finset.univ.image e)
  simpa only [Finset.card_image_of_injective _ e.injective,Finset.card_univ] using h

end Thorp.Specht

namespace Thorp.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma relabelled_tuple_dimension (μ : YoungDiagram) (e : α ≃ Cell μ) (f : ι ↪ α) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction f (relabelledUnitary μ e)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(relabelledTupleFixed μ e f).finrank_eq]
  exact tupleFixed_dimension μ (f.trans e.toEmbedding)

end Thorp.Specht


end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_MainStatement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.DimensionEstimates
open scoped BigOperators

lemma log_factorial_upper_binary (n : ℕ) (hn : 0<n) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-Real.log 2*((n:ℝ)-1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hb : (2:ℝ) ≤ (1+(n:ℝ)⁻¹)^n := by
      have h := one_add_mul_le_pow (by have := inv_nonneg.mpr hn0.le; linarith : (-2:ℝ)≤(n:ℝ)⁻¹) n
      norm_num [mul_inv_cancel₀ hn0.ne'] at h ⊢
      exact h
    have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) hb
    rw [Real.log_pow] at hl
    have hs : Real.log (1+(n:ℝ)⁻¹)=Real.log ((n:ℝ)+1)-Real.log n := by
      rw [←Real.log_div (by positivity) hn0.ne']
      congr 1
      field_simp
    rw [hs] at hl
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

lemma log_factorial_lower (n : ℕ) (hn : 0<n) :
    (n:ℝ)*Real.log n-n+1 ≤ Real.log (n.factorial:ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hl := Real.log_le_sub_one_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl hn0.le
    have he : (n:ℝ)*(((n:ℝ)+1)/n-1)=1 := by field_simp; ring
    rw [he] at hh
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

lemma log_factorial_upper (n : ℕ) (hn : 0<n) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-n+Real.log n+1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hl := Real.one_sub_inv_le_log_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl (show 0≤(n:ℝ)+1 by positivity)
    have he : ((n:ℝ)+1)*(1-(((n:ℝ)+1)/n)⁻¹)=1 := by field_simp; ring
    rw [he] at hh
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
open scoped Classical

omit [Fintype I] in
lemma fiberWeight_nonneg (f : X → I) (i : I) : 0≤fiberWeight f i := Nat.cast_nonneg _

omit [Fintype I] in
lemma fiberWeight_pos (f : X → I) (x : X) : 0<fiberWeight f (f x) := by
  let : Nonempty {y // f y=f x} := ⟨⟨x,rfl⟩⟩
  exact Nat.cast_pos.mpr Fintype.card_pos

lemma fiber_sum (f : X → I) (u : I → ℝ) :
    ∑ x, u (f x)=∑ i, fiberWeight f i*u i := by
  rw [←Equiv.sum_comp (Equiv.sigmaFiberEquiv f)]
  simp only [Equiv.sigmaFiberEquiv_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ x : {x // f x=i}, u (f x)) = ∑ _x : {x // f x=i}, u i :=
      Finset.sum_congr rfl (fun x _ => congrArg u x.property)
    _ = _ := by simp [fiberWeight]

lemma sum_fiberWeight (f : X → I) : ∑ i, fiberWeight f i=Fintype.card X := by
  have h := fiber_sum f (fun _ => 1)
  simpa using h.symm

theorem incidence_entropy (f : X → I) (g : X → J)
    (hinj : Function.Injective (fun x => (f x,g x))) :
    (∑ i, fiberWeight f i*Real.log (fiberWeight f i))+
      (∑ j, fiberWeight g j*Real.log (fiberWeight g j)) ≤
        (Fintype.card X:ℝ)*Real.log (Fintype.card X) := by
  by_cases hX : Nonempty X
  · let : Nonempty X := hX
    have hN : (0:ℝ)<Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
    have hprod : ∑ x, fiberWeight f (f x)*fiberWeight g (g x) ≤ (Fintype.card X:ℝ)^2 := by
      calc
        _ ≤ ∑ p : I × J, fiberWeight f p.1*fiberWeight g p.2 := by
          calc
            _ = ∑ p ∈ Finset.univ.image (fun x => (f x,g x)), fiberWeight f p.1*fiberWeight g p.2 := by
              rw [Finset.sum_image (fun x _ y _ h => hinj h)]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun p _ _ => mul_nonneg (fiberWeight_nonneg f p.1) (fiberWeight_nonneg g p.2))
        _ = _ := by
          rw [Fintype.sum_prod_type]
          simp_rw [←Finset.mul_sum]
          rw [←Finset.sum_mul,sum_fiberWeight,sum_fiberWeight,pow_two]
    have hdiv : (∑ x, fiberWeight f (f x)*fiberWeight g (g x))/(Fintype.card X:ℝ) ≤ Fintype.card X := by
      apply (div_le_iff₀ hN).mpr
      simpa only [pow_two] using hprod
    have hl (x : X) := Real.log_le_sub_one_of_pos
      (show 0<fiberWeight f (f x)*fiberWeight g (g x)/(Fintype.card X:ℝ) from
        div_pos (mul_pos (fiberWeight_pos f x) (fiberWeight_pos g x)) hN)
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hl x)
    simp_rw [Real.log_div (mul_pos (fiberWeight_pos f _) (fiberWeight_pos g _)).ne' hN.ne',
      Real.log_mul (fiberWeight_pos f _).ne' (fiberWeight_pos g _).ne'] at hs
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,
      fiber_sum f (fun i => Real.log (fiberWeight f i)),
      fiber_sum g (fun j => Real.log (fiberWeight g j)),
      Finset.sum_sub_distrib,←Finset.sum_div] at hs
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
    linarith
  · let : IsEmpty X := not_nonempty_iff.mp hX
    have hf (i : I) : fiberWeight f i=0 := by simp [fiberWeight]
    have hg (j : J) : fiberWeight g j=0 := by simp [fiberWeight]
    simp [hf,hg]

end Thorp.DimensionEstimates

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical

lemma log_factorial_upper_binary_all (n : ℕ) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-Real.log 2*((n:ℝ)-1) := by
  by_cases hn : n=0
  · subst n
    simpa using (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  · exact log_factorial_upper_binary n (Nat.pos_of_ne_zero hn)

lemma log_fiber_factorials {X I : Type*} [Fintype X] [Fintype I] (f : X → I) :
    Real.log ((∏ i, (Fintype.card {x // f x=i}).factorial : ℕ):ℝ) ≤
      ∑ i, fiberWeight f i*Real.log (fiberWeight f i) -
        Real.log 2*((Fintype.card X:ℝ)-Fintype.card I) := by
  rw [Nat.cast_prod,Real.log_prod (fun _ _ => by positivity)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    log_factorial_upper_binary_all (Fintype.card {x // f x=i}))
  change ∑ i, Real.log ((Fintype.card {x // f x=i}).factorial:ℝ) ≤
    ∑ i, (fiberWeight f i*Real.log (fiberWeight f i)-Real.log 2*(fiberWeight f i-1)) at h
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_sub_distrib,sum_fiberWeight] at h
  simpa using h

theorem dimension_log_from_incidence {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    [Nonempty X] (f : X → I) (g : X → J)
    (hinj : Function.Injective (fun x => (f x,g x))) (D : ℕ)
    (hD : (Fintype.card X).factorial ≤ D *
      (∏ i, (Fintype.card {x // f x=i}).factorial) *
      (∏ j, (Fintype.card {x // g x=j}).factorial)) :
    ((2*Real.log 2-1)*(Fintype.card X:ℝ)-
      Real.log 2*((Fintype.card I:ℝ)+Fintype.card J)+1) ≤ Real.log D := by
  have hd : 0<D := by
    by_contra h
    have : D=0 := by omega
    simp [this] at hD
    exact (Nat.factorial_pos _).ne' hD
  have hf := log_fiber_factorials f
  have hg := log_fiber_factorials g
  have hi := incidence_entropy f g hinj
  have hlo := log_factorial_lower (Fintype.card X) Fintype.card_pos
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<(Fintype.card X).factorial)
    (show ((Fintype.card X).factorial:ℝ) ≤ D *
      (∏ i, (Fintype.card {x // f x=i}).factorial) *
      (∏ j, (Fintype.card {x // g x=j}).factorial) by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hlog
  nlinarith


lemma scaled_binEntropy (N j : ℝ) (hN : 0<N) (hj : 0<j) (hjN : j<N) :
    N*Real.binEntropy (j/N)=N*Real.log N-j*Real.log j-(N-j)*Real.log (N-j) := by
  have hsub : 0<N-j := sub_pos.mpr hjN
  have he : 1-j/N=(N-j)/N := by field_simp
  unfold Real.binEntropy
  rw [he,Real.log_inv,Real.log_inv,Real.log_div hj.ne' hN.ne',
    Real.log_div hsub.ne' hN.ne']
  field_simp
  ring

lemma log_choose_lower_entropy (N j : ℕ) (hj : 0<j) (hjN : j<N) :
    (N:ℝ)*Real.binEntropy ((j:ℝ)/N)-2*Real.log N-1 ≤ Real.log (N.choose j:ℝ) := by
  have hN : 0<N := lt_trans hj hjN
  have ht : 0<N-j := Nat.sub_pos_of_lt hjN
  have hj0 : (0:ℝ)<j := by exact_mod_cast hj
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hjN0 : (j:ℝ)<N := by exact_mod_cast hjN
  have hchoose : (0:ℝ)<N.choose j := by exact_mod_cast Nat.choose_pos hjN.le
  have hfac := congrArg (fun n : ℕ => Real.log (n:ℝ)) (Nat.choose_mul_factorial_mul_factorial hjN.le)
  simp only [Nat.cast_mul] at hfac
  rw [Real.log_mul (mul_pos hchoose (by positivity)).ne' (by positivity),
    Real.log_mul hchoose.ne' (by positivity)] at hfac
  have hlo := log_factorial_lower N hN
  have hji := log_factorial_upper j hj
  have hti := log_factorial_upper (N-j) ht
  have hjlog := Real.log_le_log hj0 hjN0.le
  have htlog := Real.log_le_log (by exact_mod_cast ht : (0:ℝ)<(N-j:ℕ))
    (by exact_mod_cast Nat.sub_le N j : ((N-j:ℕ):ℝ)≤N)
  rw [Nat.cast_sub hjN.le] at hti htlog
  rw [scaled_binEntropy N j hN0 hj0 hjN0]
  linarith

lemma binEntropy_three_quarters :
    Real.binEntropy (3/4:ℝ)=2*Real.log 2-(3/4:ℝ)*Real.log 3 := by
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  unfold Real.binEntropy
  norm_num only [show (1-(3/4:ℝ))=1/4 by norm_num]
  rw [Real.log_div (by norm_num) (by norm_num),h4]
  ring

lemma entropyGap_pos : 0<entropyGap := by
  unfold entropyGap
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

lemma entropyGap_eq : entropyGap=(5*Real.log 2-3*Real.log 3)/3 := by
  unfold entropyGap
  rw [Real.log_div (by norm_num) (by norm_num),show (32:ℝ)=2^5 by norm_num,
    show (27:ℝ)=3^3 by norm_num,Real.log_pow,Real.log_pow]
  norm_num

lemma binEntropy_tail_lower (q : ℝ) (hq : 0≤q) (hq' : q≤3/4) :
    q*Real.log 2+entropyGap*q ≤ Real.binEntropy q := by
  have hc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)
    (show (3/4:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)
    (show 0≤1-4*q/3 by linarith) (show 0≤4*q/3 by positivity)
    (show (1-4*q/3)+(4*q/3)=1 by ring)
  simp only [Real.binEntropy_zero,binEntropy_three_quarters,smul_eq_mul,mul_zero,zero_add] at hc
  have he : 4*q/3*(3/4:ℝ)=q := by ring
  rw [he] at hc
  rw [entropyGap_eq]
  linarith

lemma log_dimension_from_binomial (N j D : ℕ) (hj : 0<j) (hjN : j<N)
    (hfrac : (j:ℝ)≤(3/4:ℝ)*N) (hD : N.choose j≤D*2^j) :
    entropyGap*(j:ℝ)-2*Real.log N-1 ≤ Real.log D := by
  have hpos : 0<N.choose j := Nat.choose_pos hjN.le
  have hd : 0<D := by nlinarith [Nat.zero_le (2^j)]
  have hN : (0:ℝ)<N := by exact_mod_cast lt_trans hj hjN
  have hm := Real.log_le_log (by exact_mod_cast hpos : (0:ℝ)<N.choose j)
    (show (N.choose j:ℝ)≤D*2^j by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hm
  have he := binEntropy_tail_lower ((j:ℝ)/N) (by positivity)
    ((div_le_iff₀ hN).mpr hfrac)
  have hel := mul_le_mul_of_nonneg_left he hN.le
  have hbin := log_choose_lower_entropy N j hj hjN
  have heq : (N:ℝ)*((j:ℝ)/N*Real.log 2+entropyGap*((j:ℝ)/N))=
      (j:ℝ)*Real.log 2+entropyGap*j := by field_simp
  rw [heq] at hel
  linarith


lemma log_choose_upper (N j : ℕ) (hN : 0<N) (hj : j≤N) :
    Real.log (N.choose j:ℝ) ≤ (j:ℝ)*Real.log N-Real.log (j.factorial:ℝ) := by
  have hh := Real.log_le_log (by exact_mod_cast Nat.choose_pos hj : (0:ℝ)<N.choose j)
    (Nat.choose_le_pow_div j N : (N.choose j:ℝ)≤(N:ℝ)^j/(j.factorial:ℝ))
  rw [Real.log_div (by positivity : (N:ℝ)^j≠0) (by positivity : (j.factorial:ℝ)≠0),Real.log_pow] at hh
  exact hh

lemma log_choose_lower (N j : ℕ) (hj : j≤N) :
    (j:ℝ)*Real.log (N+1-j:ℕ)-Real.log (j.factorial:ℝ) ≤ Real.log (N.choose j:ℝ) := by
  have hp : 0<N+1-j := by omega
  have hh := Real.log_le_log (by positivity : (0:ℝ)<((N+1-j:ℕ):ℝ)^j/(j.factorial:ℝ))
    (Nat.pow_le_choose j N : (((N+1-j:ℕ):ℝ)^j)/(j.factorial:ℝ)≤N.choose j)
  rw [Real.log_div (by positivity : (((N+1-j:ℕ):ℝ)^j)≠0) (by positivity : (j.factorial:ℝ)≠0),Real.log_pow] at hh
  exact hh

lemma footprint_log_bound (N k j D m : ℕ) (hN : 0<N) (hk : j≤k) (hj : j≤N)
    (hD : 0<D) (hfoot : D * k.choose j ≤ m * N.choose j) :
    Real.log D-(j:ℝ)*(Real.log N-Real.log (k+1-j:ℕ)) ≤ Real.log m := by
  have hkpos := Nat.choose_pos hk
  have hprod : 0<D*k.choose j := Nat.mul_pos hD hkpos
  have hm : 0 < m := by
    by_contra h
    have he : m=0 := by omega
    simp only [he,zero_mul] at hfoot
    omega
  have hh := Real.log_le_log (by exact_mod_cast hprod : (0:ℝ)<D*k.choose j)
    (show (D:ℝ)*k.choose j≤ m*N.choose j by exact_mod_cast hfoot)
  rw [Real.log_mul (by positivity) (by exact_mod_cast hkpos.ne'),
    Real.log_mul (by positivity) (by exact_mod_cast (Nat.choose_pos hj).ne')] at hh
  have hlo := log_choose_lower k j hk
  have hup := log_choose_upper N j hN hj
  nlinarith

lemma log_factorial_le_mul_log (j : ℕ) (_hj : 0<j) :
    Real.log (j.factorial:ℝ)≤(j:ℝ)*Real.log j := by
  have h := Real.log_le_log (by positivity : (0:ℝ)<j.factorial)
    (show (j.factorial:ℝ)≤(j:ℝ)^j by exact_mod_cast Nat.factorial_le_pow j)
  simpa only [Real.log_pow] using h

lemma near_row_log_dimension (N j D : ℕ) (hj : 0<j) (hsmall : 2*j≤N)
    (hD : N.choose j≤D*2^j) :
    (j:ℝ)*(Real.log ((N:ℝ)/j)-2*Real.log 2) ≤ Real.log D := by
  have hjN : j≤N := by omega
  have hN : 0<N := by omega
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hn : 0<N+1-j := by omega
  have hnreal : (N:ℝ)/2≤(N+1-j:ℕ) := by
    rw [Nat.cast_sub (by omega : j≤N+1),Nat.cast_add,Nat.cast_one]
    have hc : 2*(j:ℝ)≤N := by exact_mod_cast hsmall
    linarith
  have hDpos : 0<D := by
    have hc := Nat.choose_pos hjN
    by_contra h
    have he : D=0 := by omega
    simp only [he,zero_mul] at hD
    omega
  have hm := Real.log_le_log (by exact_mod_cast Nat.choose_pos hjN : (0:ℝ)<N.choose j)
    (show (N.choose j:ℝ)≤D*2^j by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hm
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(N:ℝ)/2) hnreal
  rw [Real.log_div hNp.ne' (by norm_num)] at hl
  have hh := log_choose_lower N j hjN
  have hf := log_factorial_le_mul_log j hj
  rw [Real.log_div hNp.ne' hjp.ne']
  nlinarith

open Filter

lemma chosenTuple_bounds (N j : ℕ) (hj : 0<j) (hx : 1≤(N:ℝ)/j)
    (hhalf : ((N:ℝ)/j)^(nearPower-1)≤1/2) :
    j ≤ chosenTuple N j ∧ chosenTuple N j≤N ∧
      (chosenTuple N j:ℝ)≤2*j*((N:ℝ)/j)^nearPower := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hj1 : (1:ℝ)≤j := by exact_mod_cast hj
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hpow : 1≤x^nearPower := Real.one_le_rpow hx (by norm_num [nearPower])
  have hceil : (j:ℝ)*x^nearPower ≤ chosenTuple N j := Nat.le_ceil _
  have hceil' : (chosenTuple N j:ℝ)<(j:ℝ)*x^nearPower+1 := Nat.ceil_lt_add_one (by positivity)
  have he : (j:ℝ)*x=N := by dsimp [x]; field_simp
  have hh : x^nearPower≤x/2 := by
    rw [Real.rpow_sub hxp,Real.rpow_one] at hhalf
    nlinarith [(div_le_iff₀ hxp).mp hhalf]
  constructor
  · exact_mod_cast (le_mul_of_one_le_right hjp.le hpow).trans hceil
  constructor
  · apply Nat.ceil_le.mpr
    change (j:ℝ)*x^nearPower≤N
    nlinarith
  · change (chosenTuple N j:ℝ)≤2*(j:ℝ)*x^nearPower
    nlinarith

lemma chosenTuple_tail_lower (N j : ℕ) (hj : 0<j)
    (hx : 2≤((N:ℝ)/j)^nearPower) :
    (j:ℝ)*((N:ℝ)/j)^nearPower/2 ≤ (chosenTuple N j+1-j:ℕ) := by
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hc : (j:ℝ)*((N:ℝ)/j)^nearPower ≤ chosenTuple N j := Nat.le_ceil _
  have hjk : j ≤ chosenTuple N j := by exact_mod_cast (by nlinarith : (j:ℝ) ≤ chosenTuple N j)
  rw [Nat.cast_sub (by omega : j ≤ chosenTuple N j+1),Nat.cast_add,Nat.cast_one]
  nlinarith

lemma chosenTuple_log_footprint (N j D m : ℕ) (hj : 0<j)
    (hN : 2*j≤N) (hD : N.choose j≤D*2^j)
    (hx : 2≤((N:ℝ)/j)^nearPower)
    (hlog : 8*Real.log 2/nearPower≤Real.log ((N:ℝ)/j))
    (hfoot : D * (chosenTuple N j).choose j ≤ m * N.choose j) :
    nearFraction*Real.log D≤Real.log m := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hxp : 0<x := by dsimp [x]; positivity
  have hdpos : 0<D := by
    have hc := Nat.choose_pos (show j≤N by omega)
    by_contra h
    have hz : D=0 := by omega
    simp only [hz,zero_mul] at hD
    omega
  have htail := chosenTuple_tail_lower N j hj hx
  have hjk : j ≤ chosenTuple N j := by
    have hc : (j:ℝ)*x^nearPower ≤ chosenTuple N j := Nat.le_ceil _
    exact_mod_cast (by nlinarith : (j:ℝ) ≤ chosenTuple N j)
  have hh := footprint_log_bound N (chosenTuple N j) j D m (by omega) hjk (by omega) hdpos hfoot
  have htlog := Real.log_le_log (by positivity : (0:ℝ)<(j:ℝ)*x^nearPower/2) htail
  rw [Real.log_div (by positivity) (by norm_num),Real.log_mul hjp.ne' (by positivity),Real.log_rpow hxp] at htlog
  have hxlog : Real.log x=Real.log N-Real.log j := Real.log_div hNp.ne' hjp.ne'
  have hdim := near_row_log_dimension N j D hj hN hD
  change (j:ℝ)*(Real.log x-2*Real.log 2)≤Real.log D at hdim
  have hh' : Real.log D-(j:ℝ)*((1-nearPower)*Real.log x+Real.log 2)≤Real.log m := by
    have hm := mul_le_mul_of_nonneg_left htlog hjp.le
    rw [hxlog] at hm
    nlinarith
  have hlg : (3-nearPower)*Real.log 2≤nearFraction*Real.log x := by
    dsimp [nearPower,nearFraction] at hlog ⊢
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    linarith
  have hlg' := mul_le_mul_of_nonneg_left hlg hjp.le
  dsimp [nearPower,nearFraction] at hh' hlg' ⊢
  nlinarith

lemma near_row_log_uniform (N j D : ℕ) (hj : 0<j) (hN : 2*j≤N)
    (hD : N.choose j≤D*2^j) (hlog : 4*Real.log 2+2≤Real.log ((N:ℝ)/j)) :
    (1/2:ℝ)*Real.log N≤Real.log D ∧ (j:ℝ)≤Real.log D := by
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hj1 : (1:ℝ)≤j := by exact_mod_cast hj
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hd := near_row_log_dimension N j D hj hN hD
  have hjlog := Real.log_le_sub_one_of_pos hjp
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : 1≤Real.log ((N:ℝ)/j) := by linarith
  have he : Real.log N=Real.log j+Real.log ((N:ℝ)/j) := by rw [Real.log_div hNp.ne' hjp.ne']; ring
  constructor
  · rw [he]
    nlinarith
  · nlinarith


lemma chosenTuple_density_bound (N j : ℕ) (hj : 0<j) (hx : 1≤(N:ℝ)/j)
    (hhalf : ((N:ℝ)/j)^(nearPower-1)≤1/2) (C : ℝ) (hC : 0≤C) :
    C*(chosenTuple N j:ℝ)*((chosenTuple N j:ℝ)/N)^(1/512:ℝ) ≤
      C*2^(1+(1/512:ℝ))*(j:ℝ)*((N:ℝ)/j)^(-tailPower) := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hNp : (0:ℝ)<N := by
    have : (0:ℝ)<(N:ℝ)/j := hxp
    exact (div_pos_iff.mp this).resolve_right (by intro h; exact (not_lt_of_ge hjp.le) h.2) |>.1
  have he : (j:ℝ)*x=N := by dsimp [x]; field_simp
  have hk := (chosenTuple_bounds N j hj hx hhalf).2.2
  change (chosenTuple N j:ℝ)≤2*(j:ℝ)*x^nearPower at hk
  have hratio : (chosenTuple N j:ℝ)/N≤2*x^(nearPower-1) := by
    rw [Real.rpow_sub hxp,Real.rpow_one]
    apply (div_le_iff₀ hNp).mpr
    rw [←he]
    have : 2*(x^nearPower/x)*((j:ℝ)*x)=2*(j:ℝ)*x^nearPower := by field_simp
    rw [this]
    exact hk
  have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(chosenTuple N j:ℝ)/N) hratio
    (by norm_num : (0:ℝ)≤1/512)
  have hmain := mul_le_mul hk hpow (by positivity) (by positivity)
  have hrpow : (2*x^(nearPower-1))^(1/512:ℝ)=
      (2:ℝ)^(1/512:ℝ)*x^((nearPower-1)*(1/512)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity),←Real.rpow_mul hxp.le]
  rw [hrpow] at hmain
  have heq : 2*(j:ℝ)*x^nearPower*((2:ℝ)^(1/512:ℝ)*x^((nearPower-1)*(1/512)))=
      (2:ℝ)^(1+(1/512:ℝ))*(j:ℝ)*x^(-tailPower) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
    have hp : nearPower+(nearPower-1)*(1/512) = -tailPower := by norm_num [nearPower,tailPower]
    rw [←hp,Real.rpow_add hxp]
    ring
  rw [heq] at hmain
  have h := mul_le_mul_of_nonneg_left hmain hC
  simpa only [mul_assoc] using h

lemma near_conditions_eventually (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, 2≤x ∧ 2≤x^nearPower ∧ x^(nearPower-1)≤1/2 ∧
      8*Real.log 2/nearPower≤Real.log x ∧ 4*Real.log 2+2≤Real.log x ∧
      C*2^(1+(1/512:ℝ))*x^(-tailPower) ≤ nearFraction/4000 := by
  have hpow := (tendsto_rpow_atTop (by norm_num [nearPower] : 0<nearPower)).eventually
    (eventually_ge_atTop (2:ℝ))
  have hhalf : ∀ᶠ x : ℝ in atTop, x^(nearPower-1)≤1/2 := by
    have h := (tendsto_rpow_neg_atTop (by norm_num [nearPower] : 0<1-nearPower)).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
    filter_upwards [h] with x hx
    simpa only [neg_sub] using hx.le
  have hdec : Tendsto (fun x : ℝ => C*2^(1+(1/512:ℝ))*x^(-tailPower)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by norm_num [tailPower] : 0<tailPower)))
  have hd := hdec.eventually (gt_mem_nhds (by norm_num [nearFraction] : (0:ℝ)<nearFraction/4000))
  filter_upwards [eventually_ge_atTop (2:ℝ),hpow,hhalf,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (8*Real.log 2/nearPower)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*Real.log 2+2)),hd] with x hx hp hh hl hl' hd
  exact ⟨hx,hp,hh,hl,hl',hd.le⟩

end Thorp.DimensionEstimates

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_InsertionPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical

section
open Filter

theorem exists_near_cutoff (C : ℝ) (hC : 0≤C) :
    ∃ X : ℝ, 2≤X ∧ ∀ (N j D m : ℕ), 0<j → X≤(N:ℝ)/j →
      N.choose j≤D*2^j →
      D * (chosenTuple N j).choose j ≤ m * N.choose j →
      j ≤ chosenTuple N j ∧ chosenTuple N j≤N ∧
      nearFraction*Real.log D≤Real.log m ∧
      C*(chosenTuple N j:ℝ)*((chosenTuple N j:ℝ)/N)^(1/512:ℝ)≤Real.log m/4000 ∧
      (1/2:ℝ)*Real.log N≤Real.log D ∧ (j:ℝ)≤Real.log D := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (near_conditions_eventually C)
  refine ⟨max 2 X,le_max_left _ _,?_⟩
  intro N j D m hj hNx hD hfoot
  have hc := hX ((N:ℝ)/j) ((le_max_right _ _).trans hNx)
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hN : 2*j≤N := by exact_mod_cast (le_div_iff₀ hjp).mp hc.1
  have hk := chosenTuple_bounds N j hj (by linarith [hc.1]) hc.2.2.1
  have hm := chosenTuple_log_footprint N j D m hj hN hD hc.2.1 hc.2.2.2.1 hfoot
  have hd := near_row_log_uniform N j D hj hN hD hc.2.2.2.2.1
  refine ⟨hk.1,hk.2.1,hm,?_,hd⟩
  apply (chosenTuple_density_bound N j hj (by linarith [hc.1]) hc.2.2.1 C hC).trans
  have hh := mul_le_mul_of_nonneg_right hc.2.2.2.2.2 hjp.le
  dsimp [nearFraction] at hm ⊢
  dsimp [nearFraction] at hh
  nlinarith [hd.2]

end

lemma amplification_numerical (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ 2*Real.exp (-Real.log m/4000) := by
  have hmp : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl : 0≤Real.log m := Real.log_nonneg hm
  have he : Real.exp (Real.log m/2)/m=Real.exp (-Real.log m/2) := by
    calc
      _ = Real.exp (Real.log m/2)/Real.exp (Real.log m) := by rw [Real.exp_log hmp]
      _ = _ := by rw [←Real.exp_sub]; congr 1; ring
  have hs : Real.sqrt (Real.exp (-Real.log m/2))=Real.exp (-Real.log m/4) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_add,he,hs]
  have h₁ : u+(Real.log m/2)*(-(1/1000:ℝ))≤ -Real.log m/4000 := by linarith
  have h₂ : -Real.log m/4≤ -Real.log m/4000 := by linarith
  linarith [Real.exp_le_exp.mpr h₁,Real.exp_le_exp.mpr h₂]

lemma amplification_absorb (x : ℝ) (hx : 8000*Real.log 2≤x) :
    2*Real.exp (-x/4000)≤Real.exp (-x/8000) := by
  rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma amplification_decay (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000)
    (hl : 8000*Real.log 2≤Real.log m) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ Real.exp (-Real.log m/8000) :=
  (amplification_numerical m u hm hu).trans (amplification_absorb _ hl)

end Thorp.DimensionEstimates

namespace Thorp.Specht
open scoped BigOperators Classical

theorem choose_tail_le_of_factorial (μ : YoungDiagram) (D : ℕ)
    (hd : μ.card.factorial ≤ D * Fintype.card (rowGroup μ) * Fintype.card (colGroup μ)) :
    μ.card.choose (μ.card-μ.rowLen 0) ≤ D * 2^(μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  have htail := card_fiberGroups_mul_le
    (fun x : Tail μ => rowIndex x.1) (fun x : Tail μ => colIndex x.1)
    (fun x y hr hc => Subtype.ext (Subtype.ext (Prod.ext (congrArg Fin.val hr) (congrArg Fin.val hc))))
  rw [tail_card] at htail
  have hc := column_group_le_tail μ
  have hr := tail_row_group μ
  simp only [←Nat.card_eq_fintype_card] at htail hc hr hd
  have hh : μ.card.factorial ≤ D * 2^j *
      ((μ.rowLen 0).factorial * j.factorial) := by
    calc
      _ ≤ _ := hd
      _ ≤ D * Nat.card (rowGroup μ) *
          (2^j * Nat.card (fiberGroup (fun x : Tail μ => colIndex x.1))) := Nat.mul_le_mul_left _ hc
      _ = D * 2^j * (μ.rowLen 0).factorial *
          (Nat.card (fiberGroup (fun x : Tail μ => rowIndex x.1)) *
           Nat.card (fiberGroup (fun x : Tail μ => colIndex x.1))) := by rw [←hr]; ring
      _ ≤ _ := by
        calc
          _ ≤ D * 2^j * (μ.rowLen 0).factorial * j.factorial :=
            Nat.mul_le_mul_left _ htail
          _ = _ := by ring
  have hj : j ≤ μ.card := Nat.sub_le _ _
  have hs : μ.card-j = μ.rowLen 0 := by dsimp [j]; have := rowLen_zero_le_card μ; omega
  have hf := Nat.choose_mul_factorial_mul_factorial hj
  rw [hs] at hf
  rw [←hf] at hh
  have hpos : 0 < (μ.rowLen 0).factorial * j.factorial := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  nlinarith

lemma card_rowGroup_transpose (μ : YoungDiagram) :
    Fintype.card (rowGroup μ.transpose) = Fintype.card (colGroup μ) := by
  rw [card_rowGroup,card_colGroup]
  apply Fintype.prod_equiv (finCongr (μ.colLen_transpose 0))
  intro i
  change (μ.transpose.rowLen i).factorial = (μ.colLen i).factorial
  rw [YoungDiagram.rowLen_transpose]

lemma card_colGroup_transpose (μ : YoungDiagram) :
    Fintype.card (colGroup μ.transpose) = Fintype.card (rowGroup μ) := by
  rw [card_colGroup,card_rowGroup]
  apply Fintype.prod_equiv (finCongr (μ.rowLen_transpose 0))
  intro i
  change (μ.transpose.colLen i).factorial = (μ.rowLen i).factorial
  rw [YoungDiagram.colLen_transpose]

lemma card_transpose (μ : YoungDiagram) : μ.transpose.card=μ.card := by
  unfold YoungDiagram.card YoungDiagram.transpose
  exact Finset.card_map _

theorem choose_column_tail_le_dimension (μ : YoungDiagram) :
    μ.card.choose (μ.card-μ.colLen 0) ≤ Module.finrank ℂ (space μ) * 2^(μ.card-μ.colLen 0) := by
  have hd := factorial_le_dimension_row_column μ
  have ht := choose_tail_le_of_factorial μ.transpose (Module.finrank ℂ (space μ))
  simp only [card_transpose,card_rowGroup_transpose,card_colGroup_transpose,YoungDiagram.rowLen_transpose] at ht
  apply ht
  nlinarith

open DimensionEstimates Filter

lemma dimension_log_incidence (μ : YoungDiagram) (hμ : 0<μ.card) :
    (2*Real.log 2-1)*(μ.card:ℝ)-Real.log 2*((μ.rowLen 0:ℝ)+μ.colLen 0)+1≤
      Real.log (Module.finrank ℂ (space μ)) := by
  let : Nonempty (Cell μ) := Fintype.card_pos_iff.mp (by simpa only [card_cell] using hμ)
  have hd := factorial_le_dimension_row_column μ
  rw [card_rowGroup,card_colGroup] at hd
  have hr (i : Fin (μ.colLen 0)) : Nat.card {x : Cell μ // rowIndex x=i}=μ.rowLen i := by
    let e : {x : Cell μ // rowIndex x=i} ≃ {x : Cell μ // row x=i} :=
      Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
    rw [Nat.card_congr e,Nat.card_congr (rowEquiv μ i),Nat.card_fin]
  have hc (i : Fin (μ.rowLen 0)) : Nat.card {x : Cell μ // colIndex x=i}=μ.colLen i := by
    let e : {x : Cell μ // colIndex x=i} ≃ {x : Cell μ // col x=i} :=
      Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
    rw [Nat.card_congr e,Nat.card_congr (columnEquiv μ i),Nat.card_fin]
  have hcell : Nat.card (Cell μ)=μ.card := by rw [Nat.card_eq_fintype_card,card_cell]
  have h := dimension_log_from_incidence (rowIndex (μ := μ)) (colIndex (μ := μ))
    (fun x y h => Subtype.ext (Prod.ext (congrArg (fun z => (z.1:ℕ)) h)
      (congrArg (fun z => (z.2:ℕ)) h))) (Module.finrank ℂ (space μ))
    (by simpa only [←Nat.card_eq_fintype_card,hr,hc,hcell] using hd)
  simpa only [card_cell,Fintype.card_fin,add_comm (μ.colLen 0:ℝ)] using h

lemma medium_dimension_raw (μ : YoungDiagram) (hμ : 0<μ.card) (δ : ℝ) (hδ : 0<δ)
    (hδ2 : δ≤1/2) (hrow : δ*(μ.card:ℝ)≤μ.card-μ.rowLen 0)
    (hcol : (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2) :
    min ((3/2:ℝ)*Real.log 2-1) (entropyGap*δ)*(μ.card:ℝ)-2*Real.log μ.card-1≤
      Real.log (Module.finrank ℂ (space μ)) := by
  let c := (3/2:ℝ)*Real.log 2-1
  have hN : (0:ℝ)<μ.card := by exact_mod_cast hμ
  have hlog : 0≤Real.log μ.card := Real.log_nonneg (by exact_mod_cast hμ)
  have hc : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hr := rowLen_zero_le_card μ
  have hcl : μ.colLen 0≤μ.card := by
    simpa only [YoungDiagram.rowLen_transpose,card_transpose] using rowLen_zero_le_card μ.transpose
  by_cases hsum : (μ.rowLen 0:ℝ)+μ.colLen 0≤(μ.card:ℝ)/2
  · have hi := dimension_log_incidence μ hμ
    have hm := mul_le_mul_of_nonneg_right (min_le_left c (entropyGap*δ)) hN.le
    dsimp [c] at hm
    nlinarith
  · have hbig : (μ.card:ℝ)/4≤μ.rowLen 0 ∨ (μ.card:ℝ)/4≤μ.colLen 0 := by
      by_contra h
      push Not at h
      linarith
    rcases hbig with hrb | hcb
    · have hj : 0<μ.card-μ.rowLen 0 := by
        rw [←Nat.cast_pos (α := ℝ),Nat.cast_sub hr]
        exact lt_of_lt_of_le (mul_pos hδ hN) hrow
      have hjN : μ.card-μ.rowLen 0<μ.card := by
        have : 0<μ.rowLen 0 := by exact_mod_cast (by linarith : (0:ℝ)<μ.rowLen 0)
        omega
      have hi := log_dimension_from_binomial μ.card (μ.card-μ.rowLen 0)
        (Module.finrank ℂ (space μ)) hj hjN
        (by rw [Nat.cast_sub hr]; linarith) (choose_tail_le_dimension μ)
      rw [Nat.cast_sub hr] at hi
      have hm := mul_le_mul_of_nonneg_right (min_le_right c (entropyGap*δ)) hN.le
      nlinarith [entropyGap_pos]
    · have hj : 0<μ.card-μ.colLen 0 := by
        rw [←Nat.cast_pos (α := ℝ),Nat.cast_sub hcl]
        linarith
      have hjN : μ.card-μ.colLen 0<μ.card := by
        have : 0<μ.colLen 0 := by exact_mod_cast (by linarith : (0:ℝ)<μ.colLen 0)
        omega
      have hi := log_dimension_from_binomial μ.card (μ.card-μ.colLen 0)
        (Module.finrank ℂ (space μ)) hj hjN
        (by rw [Nat.cast_sub hcl]; linarith) (choose_column_tail_le_dimension μ)
      rw [Nat.cast_sub hcl] at hi
      have hm := mul_le_mul_of_nonneg_right (min_le_right c (entropyGap*δ)) hN.le
      have ht := mul_le_mul_of_nonneg_left (show δ*(μ.card:ℝ)≤(μ.card:ℝ)-μ.colLen 0 by nlinarith) entropyGap_pos.le
      linarith

end Thorp.Specht

namespace Thorp.DimensionEstimates

open Filter

lemma log_error_eventually (a : ℝ) (ha : 0<a) :
    ∀ᶠ N : ℕ in atTop, 2*Real.log N+1≤(a/2)*(N:ℝ) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.isLittleO_log_id_atTop.bound (by linarith : 0<a/8))
  have hg := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4/a))
  filter_upwards [h,hg,eventually_ge_atTop 1] with N h hg hN
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn),id_eq,abs_of_nonneg (by positivity : (0:ℝ)≤N)] at h
  have hh : 4≤(N:ℝ)*a := (div_le_iff₀ ha).mp hg
  linarith

end Thorp.DimensionEstimates

namespace Thorp.Specht
open scoped BigOperators Classical
open DimensionEstimates Filter

theorem medium_dimension (δ : ℝ) (hδ : 0<δ) (hδ2 : δ≤1/2) :
    ∃ h : ℝ, 0<h ∧ ∀ᶠ N : ℕ in atTop, ∀ μ : YoungDiagram, μ.card=N →
      δ*(N:ℝ)≤N-μ.rowLen 0 → (μ.colLen 0:ℝ)≤(N:ℝ)/2 →
      h*(N:ℝ)≤Real.log (Module.finrank ℂ (space μ)) := by
  let a := min ((3/2:ℝ)*Real.log 2-1) (entropyGap*δ)
  have ha : 0<a := by
    apply lt_min
    · nlinarith [Real.log_two_gt_d9]
    · exact mul_pos entropyGap_pos hδ
  refine ⟨a/2,by positivity,?_⟩
  filter_upwards [log_error_eventually a ha,eventually_ge_atTop 1] with N hN hn
  intro μ hμ hr hc
  have hp : 0<μ.card := by omega
  have hh := medium_dimension_raw μ hp δ hδ hδ2 (by simpa only [hμ] using hr) (by simpa only [hμ] using hc)
  rw [hμ] at hh
  change a*(N:ℝ)-2*Real.log N-1≤_ at hh
  linarith

end Thorp.Specht

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite DimensionEstimates Filter

lemma dimension_pos (μ : YoungDiagram) : 0 < Module.finrank ℂ (space μ) := by
  have h := factorial_le_dimension_row_column μ
  by_contra hn
  have hz : Module.finrank ℂ (space μ)=0 := by omega
  rw [hz,zero_mul,zero_mul] at h
  exact (Nat.factorial_pos μ.card).not_ge h

lemma near_numerical_cutoff :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ (N j D : ℕ), 0 < j → X ≤ (N:ℝ)/j → N.choose j ≤ D * 2^j →
      ∃ k : ℕ, j ≤ k ∧ k ≤ N ∧ ∀ m : ℕ, D * k.choose j ≤ m * N.choose j →
        nearFraction * Real.log D ≤ Real.log m ∧
        densityConstant * (k:ℝ) * ((k:ℝ)/N)^(1/512:ℝ) ≤ Real.log m/4000 ∧
        (1/2:ℝ) * Real.log N ≤ Real.log D ∧ (j:ℝ) ≤ Real.log D := by
  obtain ⟨X,hX,h⟩ := exists_near_cutoff densityConstant densityConstant_pos.le
  refine ⟨X,hX,?_⟩
  intro N j D hj hx hd
  have hjN : j ≤ N := by
    have hjp : (0:ℝ) < j := by exact_mod_cast hj
    have hh : (j:ℝ) ≤ N := by
      have := (le_div_iff₀ hjp).mp (hX.trans hx)
      linarith
    exact_mod_cast hh
  have hc : 1 ≤ N.choose j := Nat.choose_pos hjN
  have hfoot : D * (chosenTuple N j).choose j ≤ (D * (chosenTuple N j).choose j) * N.choose j :=
    Nat.le_mul_of_pos_right _ hc
  have hh := h N j D _ hj hx hd hfoot
  refine ⟨chosenTuple N j,hh.1,hh.2.1,?_⟩
  intro m hm
  exact (h N j D m hj hx hd hm).2.2

theorem near_row_spectral :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ),
      0 < μ.card-μ.rowLen 0 → X ≤ (μ.card:ℝ)/(μ.card-μ.rowLen 0:ℕ) →
      32768000 * Real.log 2 ≤ (1/2:ℝ) * Real.log μ.card →
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
        Real.exp (-(nearFraction/8000) * Real.log (Module.finrank ℂ (space μ))) ∧
      (1/2:ℝ) * Real.log μ.card ≤ Real.log (Module.finrank ℂ (space μ)) ∧
      (μ.card-μ.rowLen 0:ℕ) ≤ Real.log (Module.finrank ℂ (space μ)) := by
  obtain ⟨X,hX,h⟩ := near_numerical_cutoff
  refine ⟨X,hX,?_⟩
  intro d μ e hj hx hlarge
  let j := μ.card-μ.rowLen 0
  let D := Module.finrank ℂ (space μ)
  have hcard : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  obtain ⟨k,hjk,hk,hnum⟩ := h μ.card j D hj hx (choose_tail_le_dimension μ)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin k) ≤ Fintype.card (Card d) by simpa only [Fintype.card_fin,card_positions,←hcard] using hk)
  let m := Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))
  have hfoot : D * k.choose j ≤ m * μ.card.choose j := by
    simpa only [Fintype.card_fin,finrank_hilbertSpace] using relabelled_tuple_dimension μ e f
  have hm : 0 < m := by
    have hc := Nat.choose_pos hjk
    have hd := dimension_pos μ
    by_contra hn
    have hz : m=0 := by omega
    rw [hz,zero_mul] at hfoot
    exact (Nat.mul_pos hd hc).not_ge hfoot
  obtain ⟨hlm,hden,hlog,hjlog⟩ := hnum m hfoot
  have ha := near_row_amplification_q77 d μ e f (hj.trans_le hjk) hm
  have hcardR : (μ.card:ℝ)=(2:ℝ)^d := by exact_mod_cast hcard
  rw [←hcardR] at ha
  have hl : 8000 * Real.log 2 ≤ Real.log m := by
    dsimp [nearFraction] at hlm
    linarith
  have hn := amplification_decay (m:ℝ) (densityConstant * k * ((k:ℝ)/μ.card)^(1/512:ℝ))
    (by exact_mod_cast hm) hden hl
  refine ⟨ha.trans (hn.trans ?_),hlog,hjlog⟩
  apply Real.exp_le_exp.mpr
  dsimp [D] at hlm
  linarith

end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_TailShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.DimensionEstimates
open Filter

lemma twopow_tendsto : Tendsto (fun d : ℕ => (2:ℝ)^d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma twopow_nat_tendsto : Tendsto (fun d : ℕ => (2:ℕ)^d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma twopow_mul_eventually (c : ℝ) (hc : 0 < c) (B : ℝ) :
    ∀ᶠ d : ℕ in atTop, B ≤ c*(2:ℝ)^d := by
  filter_upwards [twopow_tendsto.eventually (eventually_ge_atTop (B/c))] with d hd
  exact (div_le_iff₀ hc).mp hd |>.trans_eq (mul_comm _ _)

end Thorp.DimensionEstimates
namespace Thorp.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates


theorem spectral_regimes_q77_oai :
    ∃ a h : ℝ, 0<a ∧ 0<h ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (μ : YoungDiagram) (e : Card d ≃ Cell μ), 0<μ.card-μ.rowLen 0 →
        (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2 →
        ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖≤
          Real.exp (-a*Real.log (Module.finrank ℂ (space μ))) ∧
        1≤Real.log (Module.finrank ℂ (space μ)) ∧
        (((1/2:ℝ)*Real.log μ.card≤Real.log (Module.finrank ℂ (space μ)) ∧
          (μ.card-μ.rowLen 0:ℕ)≤Real.log (Module.finrank ℂ (space μ))) ∨
          h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ))) := by
  obtain ⟨X,hX,hnear⟩ := near_row_spectral
  have hXpos : 0<X := by linarith
  have hδ : 0<(1:ℝ)/X := by positivity
  have hδ2 : (1:ℝ)/X≤1/2 := (div_le_iff₀ hXpos).mpr (by linarith)
  obtain ⟨h,hh,hmedium⟩ := medium_dimension (1/X) hδ hδ2
  obtain ⟨a₀,ha₀,hlarge⟩ := exponential_dimension_spectral_q77 h hh
  let a := min (nearFraction/8000) a₀
  have ha : 0<a := lt_min (by norm_num [nearFraction]) ha₀
  refine ⟨a,h,ha,hh,?_⟩
  have hl := (Real.tendsto_log_atTop.comp twopow_tendsto).eventually
    (eventually_ge_atTop (2*max (32768000*Real.log 2) 1))
  filter_upwards [hlarge,twopow_nat_tendsto.eventually hmedium,hl,
    twopow_mul_eventually h hh 1] with d hspec hdim hlog h1
  intro μ e hj hc
  simp only [Function.comp_apply] at hlog
  have hcard : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  have hcardR : (μ.card:ℝ)=(2:ℝ)^d := by exact_mod_cast hcard
  have hμlog : max (32768000*Real.log 2) 1≤(1/2:ℝ)*Real.log μ.card := by rw [hcardR]; linarith
  by_cases hx : X≤(μ.card:ℝ)/(μ.card-μ.rowLen 0:ℕ)
  · obtain ⟨hs,hl,hjD⟩ := hnear d μ e hj hx ((le_max_left _ _).trans hμlog)
    have h1D : 1≤Real.log (Module.finrank ℂ (space μ)) := ((le_max_right _ _).trans hμlog).trans hl
    refine ⟨hs.trans (Real.exp_le_exp.mpr ?_),h1D,Or.inl ⟨hl,hjD⟩⟩
    have hp := mul_le_mul_of_nonneg_right (min_le_left (nearFraction/8000) a₀) (by linarith : 0≤Real.log (Module.finrank ℂ (space μ)))
    dsimp [a]
    linarith
  · have htail : (1/X)*(μ.card:ℝ)≤(μ.card:ℝ)-μ.rowLen 0 := by
      have hjR : (0:ℝ)<(μ.card-μ.rowLen 0:ℕ) := by exact_mod_cast hj
      have hh := (div_lt_iff₀ hjR).mp (lt_of_not_ge hx)
      have hs : ((μ.card-μ.rowLen 0:ℕ):ℝ)=(μ.card:ℝ)-μ.rowLen 0 := by
        rw [Nat.cast_sub (rowLen_zero_le_card μ)]
      rw [hs] at hh
      have hd : (μ.card:ℝ)/X≤(μ.card:ℝ)-μ.rowLen 0 :=
        (div_le_iff₀ hXpos).mpr (by nlinarith)
      convert hd using 1 <;> first | rfl | ring
    have hdim' : h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ)) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using
        hdim μ hcard (by simpa only [hcard] using htail) (by simpa only [hcard] using hc)
    have h1D := h1.trans hdim'
    refine ⟨(hspec μ e hdim').trans (Real.exp_le_exp.mpr ?_),h1D,Or.inr hdim'⟩
    have hp := mul_le_mul_of_nonneg_right (min_le_right (nearFraction/8000) a₀) (by linarith : 0≤Real.log (Module.finrank ℂ (space μ)))
    dsimp [a]
    linarith

end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end

theorem solution : type_of% @OAI.ThorpNine.Adaptive.Thorp.Specht.spectral_regimes_q77_oai := @OAI.ThorpNine.Adaptive.Thorp.Specht.spectral_regimes_q77_oai
