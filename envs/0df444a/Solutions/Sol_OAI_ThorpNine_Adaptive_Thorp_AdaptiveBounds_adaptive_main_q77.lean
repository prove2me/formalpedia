-- Prove2me | solution 1 for OAI.ThorpNine.Adaptive.Thorp.AdaptiveBounds.adaptive_main_q77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:58:08.098497+00:00
-- url     : https://prove2.me/submissions/57339b49-14fb-4be1-b54d-460dc557e891

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000
import Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_AdaptiveBounds_dimension_trace_bound_q77
import Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_Casimir_eventual_level_contraction_q77
import Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_Specht_spectral_regimes_q77

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
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma finiteMean_congr {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : finiteMean f = finiteMean g := by
  unfold finiteMean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

lemma finiteMean_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω → ℝ) :
    finiteMean f = finiteMean (fun ω => f (e.symm ω)) := by
  unfold finiteMean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun ω => by simp)

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma butterflyPerm_step (d : ℕ)
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool) :
    butterflyPerm (d+1) (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ))) =
    pairSwitch ξ * childLift (fun b => butterflyPerm d (decodeButterfly d (if b then c.2 else c.1))) := by
  change pairSwitch (fun y => (coinStepEquiv d).symm (c,ξ) (Sum.inl y)) *
    childLift (fun b => butterflyPerm d (decodeButterfly d
      (fun i => (coinStepEquiv d).symm (c,ξ) (Sum.inr (b,i))))) = _
  apply congrArg₂ (· * ·)
  · rfl
  · apply congrArg childLift
    funext b
    apply congrArg (fun ω => butterflyPerm d (decodeButterfly d ω))
    funext i
    cases b <;> rfl

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_BenesCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma childLift_inv (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    (childLift p)⁻¹ = childLift (fun b => (p b)⁻¹) := rfl

lemma pairSwitch_inv (d : ℕ) (ξ : Card d → Bool) : (pairSwitch ξ)⁻¹ = pairSwitch ξ := rfl

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

lemma palindromePerm_reverse (d : ℕ) (ω : BenesCoins d) :
    palindromePerm d (ω.2,ω.1) = (palindromePerm d ω)⁻¹ := by
  simp only [palindromePerm,mul_inv_rev]
  rfl

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


section Symmetrizer
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

lemma symmetrizer_mul (H : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (h : H) :
    symmetrizer H ρ * ρ h = symmetrizer H ρ := by
  rw [symmetrizer,Finset.sum_mul]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => by simp [←map_mul])

lemma symmetrizer_eq_zero_of_neg (H : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (h : H) (v : V) (hv : ρ h v = -v) :
    symmetrizer H ρ v = 0 := by
  have hh := congrArg (fun T : Module.End ℂ V => T v) (symmetrizer_mul H ρ h)
  change symmetrizer H ρ (ρ h v) = symmetrizer H ρ v at hh
  rw [hv,map_neg] at hh
  have h2 : (2:ℂ) • symmetrizer H ρ v = 0 := by
    rw [two_smul]
    nth_rw 1 [←hh]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

omit [Fintype α] in
lemma swap_mem_fiberGroup {β : Type*} (f : α → β) (x y : α) (hf : f x = f y) :
    Equiv.swap x y ∈ fiberGroup f := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using hf.symm
  by_cases hy : z=y
  · subst z; simpa using hf
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

end Symmetrizer

lemma swap_polytabloid {μ : YoungDiagram} (x y : Cell μ) (hne : x ≠ y)
    (hcol : col x = col y) :
    tabloidRep μ (Equiv.swap x y) (polytabloid μ) = -polytabloid μ := by
  have h := action_alternator_apply (colGroup μ) (tabloidRep μ)
    ⟨Equiv.swap x y,swap_mem_colGroup x y hcol⟩ (delta (baseTabloid μ))
  simpa only [polytabloid,permSign_swap hne,neg_one_smul] using h

theorem tall_column_average_zero (μ : YoungDiagram) {β : Type*} [Fintype β]
    (f : Cell μ → β) (j : ℕ) (hj : Fintype.card β < μ.colLen j)
    (v : Tabloid μ → ℂ) (hv : v ∈ space μ) :
    symmetrizer (fiberGroup f) (tabloidRep μ) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p,rfl⟩ := hv
    have hcard : Fintype.card β < Fintype.card {x : Cell μ // col x = j} := by
      rw [Fintype.card_congr (columnEquiv μ j),Fintype.card_fin]
      exact hj
    obtain ⟨x,y,hne,hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun x : {x : Cell μ // col x = j} => f (p x.1)) hcard
    have hxy : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    let h : fiberGroup f := ⟨Equiv.swap (p x.1) (p y.1),swap_mem_fiberGroup f _ _ hf⟩
    apply symmetrizer_eq_zero_of_neg _ _ h
    change tabloidRep μ (Equiv.swap (p x.1) (p y.1))
      (tabloidRep μ p (polytabloid μ)) = -tabloidRep μ p (polytabloid μ)
    rw [←Module.End.mul_apply,←map_mul,←Equiv.mul_swap_eq_swap_mul]
    rw [map_mul,Module.End.mul_apply,swap_polytabloid x.1 y.1 hxy (x.2.trans y.2.symm),map_neg]
  | zero => exact map_zero _
  | add v w hv hw ihv ihw => simp only [map_add,ihv,ihw,add_zero]
  | smul a v hv ih => simp only [map_smul,ih,smul_zero]


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

end FiberGroup

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

lemma card_rowGroup (μ : YoungDiagram) :
    Fintype.card (rowGroup μ) = ∏ i : Fin (μ.colLen 0), (μ.rowLen i).factorial := by
  rw [←Nat.card_eq_fintype_card,rowGroup,nat_card_fiberGroup]
  simp only [Nat.card_eq_fintype_card]
  simp only [card_row_fiber]

lemma rowLen_zero_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.card := by
  have h := Fintype.card_subtype_le (fun x : Cell μ => row x=0)
  rwa [Fintype.card_congr (rowEquiv μ 0),Fintype.card_fin,card_cell] at h

end Thorp.Specht

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_inner_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v w : V) :
    inner ℂ v (ρ g⁻¹ w) = inner ℂ (ρ g v) w := by
  have h := hρ g v (ρ g⁻¹ w)
  have he : ρ g (ρ g⁻¹ w) = w := by
    change (ρ g * ρ g⁻¹) w = w
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  rw [he] at h
  exact h.symm

end Thorp.UnitaryFinite

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_norm (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v : V) :
    ‖ρ g v‖=‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),hρ,norm_eq_sqrt_re_inner (𝕜 := ℂ)]

omit [Fintype G] in
lemma continuousRepresentation_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    ‖continuousRepresentation ρ g‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [continuousRepresentation_apply,unitary_norm ρ hρ,one_mul,le_refl]

omit [Fintype G] in
lemma continuousRepresentation_adjoint (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    (continuousRepresentation ρ g).adjoint=continuousRepresentation ρ g⁻¹ := by
  ext w
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (unitary_inner_inv ρ hρ g v w).symm

lemma weightedOperator_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, 0≤p g) : ‖weightedOperator ρ p‖ ≤ ∑ g, p g := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp g)]
  exact mul_le_of_le_one_right (hp g) (continuousRepresentation_norm_le ρ hρ g)

lemma weightedOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, p g⁻¹=p g) : IsSelfAdjoint (weightedOperator ρ p) := by
  change (weightedOperator ρ p).adjoint=weightedOperator ρ p
  unfold weightedOperator
  rw [map_sum]
  simp only [map_smulₛₗ,Complex.conj_ofReal,continuousRepresentation_adjoint ρ hρ]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp [hp]

lemma uniformOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsSelfAdjoint (uniformOperator ρ) := weightedOperator_symmetric ρ hρ _ (fun _ => rfl)

lemma uniformOperator_left (ρ : Representation ℂ G V) (g : G) :
    continuousRepresentation ρ g * uniformOperator ρ=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma uniformOperator_right (ρ : Representation ℂ G V) (g : G) :
    uniformOperator ρ * continuousRepresentation ρ g=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

lemma uniformOperator_idempotent (ρ : Representation ℂ G V) :
    IsIdempotentElem (uniformOperator ρ) := by
  change uniformOperator ρ * uniformOperator ρ=uniformOperator ρ
  nth_rw 1 [uniformOperator,weightedOperator]
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,Finset.sum_const,Finset.card_univ,
    ←Nat.cast_smul_eq_nsmul ℂ,smul_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma uniformOperator_projection (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsStarProjection (uniformOperator ρ) :=
  ⟨uniformOperator_idempotent ρ,uniformOperator_symmetric ρ hρ⟩

lemma weighted_uniform_left (ρ : Representation ℂ G V) (p : G → ℝ) :
    weightedOperator ρ p * uniformOperator ρ=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

lemma weighted_uniform_right (ρ : Representation ℂ G V) (p : G → ℝ) :
    uniformOperator ρ * weightedOperator ρ p=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,uniformOperator_right,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

theorem doeblin_off_invariants (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (ε : ℝ)
    (hminor : ∀ g, ε/(Fintype.card G:ℝ)≤p g) :
    ‖weightedOperator ρ p * (1-uniformOperator ρ)‖≤1-ε := by
  let q : G → ℝ := fun g => p g-ε/(Fintype.card G:ℝ)
  have hq : ∀ g, 0≤q g := fun g => sub_nonneg.mpr (hminor g)
  have hcard : (Fintype.card G:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ g,q g=1-ε := by
    simp only [q,Finset.sum_sub_distrib,hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have he : weightedOperator ρ p=weightedOperator ρ q+(ε:ℂ) • uniformOperator ρ := by
    simp only [uniformOperator,weightedOperator]
    rw [Finset.smul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    simp only [q,Complex.ofReal_sub,Complex.ofReal_div,smul_smul,←add_smul,
      Complex.ofReal_inv,Complex.ofReal_natCast]
    congr 1
    field_simp
    ring
  have hz : uniformOperator ρ*(1-uniformOperator ρ)=0 := by
    rw [mul_sub,mul_one,(uniformOperator_idempotent ρ).eq,sub_self]
  rw [he,add_mul,smul_mul_assoc,hz,smul_zero,add_zero]
  calc
    _ ≤ ‖weightedOperator ρ q‖*‖1-uniformOperator ρ‖ := norm_mul_le _ _
    _ ≤ (1-ε)*1 := mul_le_mul (by rw [←hsum]; exact weightedOperator_norm_le ρ hρ q hq)
      ((uniformOperator_projection ρ hρ).one_sub.norm_le _) (norm_nonneg _)
      (by rw [←hsum]; exact Finset.sum_nonneg (fun g _ => hq g))
    _ = _ := mul_one _

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma weightedOperator_conv (ρ : Representation ℂ G V) (p q : G → ℝ) :
    weightedOperator ρ (FiniteConvolution.conv p q)=weightedOperator ρ p*weightedOperator ρ q := by
  unfold weightedOperator FiniteConvolution.conv
  simp only [Complex.ofReal_sum,Finset.sum_smul]
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,←map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
  intro g
  simp [Complex.ofReal_mul,mul_comm]

lemma weightedOperator_power (ρ : Representation ℂ G V) (p : G → ℝ) (n : ℕ) :
    weightedOperator ρ (FiniteConvolution.power p n)=(weightedOperator ρ p)^n := by
  induction n with
  | zero => simp [FiniteConvolution.power,weightedOperator]
  | succ n ih => rw [FiniteConvolution.power,weightedOperator_conv,ih,pow_succ']

lemma off_invariants_pow (ρ : Representation ℂ G V) (p : G → ℝ)
    (hp : ∑ g,p g=1) (n : ℕ) (hn : n≠0) :
    (weightedOperator ρ p-uniformOperator ρ)^n=
      (weightedOperator ρ p)^n*(1-uniformOperator ρ) := by
  have hAP := weighted_uniform_left ρ p
  have hPA := weighted_uniform_right ρ p
  rw [hp,one_smul] at hAP hPA
  have hc : Commute (weightedOperator ρ p) (1-uniformOperator ρ) := by
    show _*_= _*_
    rw [mul_sub,sub_mul,mul_one,one_mul,hAP,hPA]
  have he : weightedOperator ρ p-uniformOperator ρ=
      weightedOperator ρ p*(1-uniformOperator ρ) := by rw [mul_sub,mul_one,hAP]
  rw [he,hc.mul_pow,((uniformOperator_idempotent ρ).one_sub).pow_eq hn]

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_pos {p : G → ℝ} (c : FiniteConvolution.Minorant p) : 0 < minorantGap c := by
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  unfold minorantGap
  linarith

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_lt_one {p : G → ℝ} (c : FiniteConvolution.Minorant p) : minorantGap c < 1 := by
  unfold minorantGap
  exact sub_lt_self _ (div_pos c.mass_pos (by positivity))

theorem norm_off_invariants_le_gap (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (hsym : ∀ g,p g⁻¹=p g)
    (c : FiniteConvolution.Minorant p) :
    ‖weightedOperator ρ p-uniformOperator ρ‖ ≤ minorantGap c := by
  have hself := (weightedOperator_symmetric ρ hρ p hsym).sub (uniformOperator_symmetric ρ hρ)
  have hbound := doeblin_off_invariants ρ hρ (FiniteConvolution.power p (2^c.exponent))
    (FiniteConvolution.sum_power hp _) c.mass c.lower
  rw [weightedOperator_power,←off_invariants_pow ρ p hp _ (by positivity),
    hself.norm_pow_two_pow] at hbound
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  have hbern := one_add_mul_le_pow
    (a := -(c.mass/(2*(2:ℝ)^c.exponent))) (by linarith : (-2:ℝ) ≤ -(c.mass/(2*(2:ℝ)^c.exponent)))
    (2^c.exponent)
  have he : 1+(2^c.exponent:ℕ)*(-(c.mass/(2*(2:ℝ)^c.exponent)))=1-c.mass/2 := by
    push_cast
    field_simp
    ring
  rw [he,show 1+ -(c.mass/(2*(2:ℝ)^c.exponent))=minorantGap c by rfl] at hbern
  by_contra h
  have hlt : minorantGap c < ‖weightedOperator ρ p-uniformOperator ρ‖ := lt_of_not_ge h
  have hpows := pow_lt_pow_left₀ hlt (minorantGap_pos c).le (by positivity : (2^c.exponent:ℕ)≠0)
  linarith [c.mass_pos]

end Thorp.UnitaryFinite
namespace Thorp
open scoped BigOperators Classical

variable {Ω G : Type*} [Fintype Ω] [Fintype G]

omit [Fintype G] in
lemma sampleLaw_equiv {Ω' : Type*} [Fintype Ω'] (P : Ω → G) (e : Ω' ≃ Ω) :
    sampleLaw (P ∘ e)=sampleLaw P := by
  funext g
  simpa only [sampleLaw,Function.comp_apply,Equiv.apply_symm_apply] using
    finiteMean_equiv e (fun ω => if P (e ω)=g then (1:ℝ) else 0)

variable [Group G]
omit [Fintype G] in
lemma sampleLaw_inverse (P : Ω → G) (g : G) :
    sampleLaw (fun ω => (P ω)⁻¹) g=sampleLaw P g⁻¹ := by
  apply finiteMean_congr
  intro ω
  rw [inv_eq_iff_eq_inv]

omit [Fintype G] in
lemma sampleLaw_symmetric (P : Ω → G) (e : Equiv.Perm Ω)
    (he : ∀ ω,P (e ω)=(P ω)⁻¹) (g : G) : sampleLaw P g⁻¹=sampleLaw P g := by
  rw [←sampleLaw_inverse]
  have hh : (fun ω => (P ω)⁻¹)=P ∘ e := funext (fun ω => (he ω).symm)
  rw [hh,sampleLaw_equiv]

end Thorp

namespace Thorp
open scoped BigOperators Classical

lemma blockGap_pos (d : ℕ) : 0<blockGap d := UnitaryFinite.minorantGap_pos _
lemma blockGap_lt_one (d : ℕ) : blockGap d<1 := UnitaryFinite.minorantGap_lt_one _

theorem palindrome_off_invariants_gap (d : ℕ) {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) (hρ : UnitaryFinite.IsUnitary ρ) :
    ‖UnitaryFinite.weightedOperator ρ (sampleLaw (palindromePerm d))-
      UnitaryFinite.uniformOperator ρ‖≤blockGap d := by
  apply UnitaryFinite.norm_off_invariants_le_gap ρ hρ _ (sampleLaw_sum _)
  exact sampleLaw_symmetric _ (Equiv.prodComm _ _) (palindromePerm_reverse d)

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_weighted (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P=weightedOperator ρ (sampleLaw P) := by
  unfold sampleOperator weightedOperator sampleLaw finiteMean
  simp only [Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ g, if P ω=g then (Fintype.card Ω:ℂ)⁻¹ • continuousRepresentation ρ g else 0 := by
      symm
      simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all

lemma sampleOperator_norm_le [Nonempty Ω] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    ‖sampleOperator ρ P‖≤1 := by
  rw [sampleOperator_weighted]
  exact (weightedOperator_norm_le ρ hρ _ (sampleLaw_nonneg _)).trans_eq (sampleLaw_sum P)

omit [Fintype G] in
lemma sampleOperator_equiv (ρ : Representation ℂ G V) (P : Ω → G) (e : Ξ ≃ Ω) :
    sampleOperator ρ (P ∘ e)=sampleOperator ρ P := by
  simp only [sampleOperator,Fintype.card_congr e,Function.comp_apply]
  rw [Equiv.sum_comp e (fun ω => continuousRepresentation ρ (P ω))]

omit [Fintype G] in
lemma sampleOperator_prod (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun ω : Ω × Ξ => P ω.1*Q ω.2)=sampleOperator ρ P*sampleOperator ρ Q := by
  simp only [sampleOperator,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,map_mul,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [mul_comm]

omit [Fintype G] in
lemma sampleOperator_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    sampleOperator ρ (fun ω => (P ω)⁻¹)=(sampleOperator ρ P).adjoint := by
  simp only [sampleOperator,map_smulₛₗ,map_sum,map_inv₀,map_natCast,
    continuousRepresentation_adjoint ρ hρ]

lemma sampleOperator_palindrome (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    sampleOperator ρ (palindromePerm d)=
      sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))*
      (sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint := by
  rw [←sampleOperator_inv ρ hρ,←sampleOperator_prod]
  rfl

end Thorp.UnitaryFinite

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

lemma unitaryRepresentation_unitary (μ : YoungDiagram) :
    UnitaryFinite.IsUnitary (G := Equiv.Perm (Cell μ)) (V := hilbertSpace μ) (unitaryRepresentation μ) := by
  intro p v w
  change inner ℂ (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ))
      (unitaryRepresentation μ p w : PermutationHilbert.H (Tabloid μ)) = _
  rw [unitaryRepresentation_coe,unitaryRepresentation_coe]
  exact (PermutationHilbert.act (tabloidAct p)).inner_map_map v w


end Thorp.Specht

namespace Thorp.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma relabelledUnitary_unitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    UnitaryFinite.IsUnitary (V := hilbertSpace μ) (relabelledUnitary μ e) := by
  intro g v w
  exact unitaryRepresentation_unitary μ (e.permCongr g) v w

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators Classical

lemma swap_mem_pointStabilizer {α : Type*} [DecidableEq α] (A : Finset α)
    (x y : α) (hx : x ∉ A) (hy : y ∉ A) : Equiv.swap x y ∈ pointStabilizer A := by
  intro z hz
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ hz)) (fun h => hy (h ▸ hz))

lemma point_symmetrizer_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.Tabloid μ → ℂ) (hv : v ∈ Specht.space μ) :
    Specht.symmetrizer (pointStabilizer A) (Specht.tabloidRep μ) v = 0 := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p,rfl⟩ := hv
    let e : {x : Specht.Cell μ // p x ∉ A} ≃ {x : Specht.Cell μ // x ∉ A} :=
      { toFun := fun x => ⟨p x.1,x.2⟩
        invFun := fun x => ⟨p.symm x.1, by simpa only [p.apply_symm_apply] using x.2⟩
        left_inv := fun x => by apply Subtype.ext; exact p.symm_apply_apply _
        right_inv := fun x => by apply Subtype.ext; exact p.apply_symm_apply _ }
    have hc : μ.rowLen 0 < Fintype.card {x : Specht.Cell μ // p x ∉ A} := by
      rw [Fintype.card_congr e, Fintype.card_subtype_compl, Specht.card_cell, Fintype.card_coe]
      have hr := Specht.rowLen_zero_le_card μ
      omega
    obtain ⟨x,y,hne,hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun x : {x : Specht.Cell μ // p x ∉ A} => Specht.colIndex x.1)
      (by simpa only [Fintype.card_fin] using hc)
    have hxy : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    let h : pointStabilizer A := ⟨Equiv.swap (p x.1) (p y.1),
      swap_mem_pointStabilizer A _ _ x.2 y.2⟩
    apply Specht.symmetrizer_eq_zero_of_neg _ _ h
    change Specht.tabloidRep μ (Equiv.swap (p x.1) (p y.1))
      (Specht.tabloidRep μ p (Specht.polytabloid μ)) = -Specht.tabloidRep μ p (Specht.polytabloid μ)
    rw [←Module.End.mul_apply, ←map_mul, ←Equiv.mul_swap_eq_swap_mul]
    rw [map_mul, Module.End.mul_apply,
      Specht.swap_polytabloid x.1 y.1 hxy (congrArg Fin.val hcol), map_neg]
  | zero => exact map_zero _
  | add v w hv hw ihv ihw => simp only [map_add,ihv,ihw,add_zero]
  | smul a v hv ih => simp only [map_smul,ih,smul_zero]

lemma point_fixed_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.Tabloid μ → ℂ) (hv : v ∈ Specht.space μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.tabloidRep μ p v = v) : v = 0 := by
  classical
  have hz := point_symmetrizer_zero μ A hA v hv
  have he : Specht.symmetrizer (pointStabilizer A) (Specht.tabloidRep μ) v =
      (Fintype.card (pointStabilizer A) : ℂ) • v := by
    simp only [Specht.symmetrizer, LinearMap.sum_apply, hfix _ (Subtype.prop _),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  rw [he] at hz
  exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

lemma point_unitary_fixed_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.hilbertSpace μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.unitaryRepresentation μ p v = v) : v = 0 := by
  let w := (Specht.spaceHilbertEquiv μ).symm v
  have hw : ∀ p, p ∈ pointStabilizer A → Specht.tabloidRep μ p w.val = w.val := by
    intro p hp
    have he := congrArg ((Specht.spaceHilbertEquiv μ).symm) (hfix p hp)
    change Specht.representation μ p w = w at he
    exact congrArg Subtype.val he
  have hz := point_fixed_zero μ A hA w.val w.prop hw
  have hw0 : w = 0 := Subtype.ext hz
  have he := congrArg (Specht.spaceHilbertEquiv μ) hw0
  simpa only [w, LinearEquiv.apply_symm_apply, map_zero] using he

lemma point_relabelled_fixed_zero {α : Type*} [Fintype α] (μ : YoungDiagram)
    (e : α ≃ Specht.Cell μ) (A : Finset α) (hA : A.card < μ.card - μ.rowLen 0)
    (v : Specht.hilbertSpace μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.relabelledUnitary μ e p v = v) : v = 0 := by
  classical
  apply point_unitary_fixed_zero μ (A.image e) (by simpa only [Finset.card_image_of_injective _ e.injective] using hA) v
  intro p hp
  have hf : e.symm.permCongr p ∈ pointStabilizer A := by
    intro x hx
    have hh := hp (e x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, hh, e.symm_apply_apply]
  have hh := hfix _ hf
  change Specht.unitaryRepresentation μ (e.permCongr (e.symm.permCongr p)) v = v at hh
  have he : e.permCongr (e.symm.permCongr p) = p := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, e.apply_symm_apply]
  simpa only [he] using hh


end Thorp.SparseContact


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

namespace Thorp.SparseContact
open scoped BigOperators Classical

lemma sweep_forward_norm {d : ℕ} (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ = ‖sweepOperator d μ e false‖ := by
  cases rev
  · rfl
  · simp only [sweepOperator, Bool.false_eq_true, ite_false, ite_true]
    rw [UnitaryFinite.sampleOperator_inv _ (Specht.relabelledUnitary_unitary μ e),
      ContinuousLinearMap.adjoint.norm_map]

lemma sweep_norm_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ ≤ 1 :=
  UnitaryFinite.sampleOperator_norm_le _ (Specht.relabelledUnitary_unitary μ e) _

end Thorp.SparseContact

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

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω : Type*} [Fintype Ω]

lemma inverse_butterfly_average_step (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    sampleOperator ρ (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹)=
      sampleOperator ρ (fun ω : Bool → (SwitchIndex d → Bool) =>
        childLift (fun b => (butterflyPerm d (decodeButterfly d (ω b)))⁻¹))*
      sampleOperator ρ (pairSwitch (d := d)) := by
  let e := ((Equiv.prodCongr (Equiv.boolArrowEquivProd (SwitchIndex d → Bool)) (Equiv.refl (Card d → Bool))).trans
    (coinStepEquiv d).symm)
  have he : (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹) ∘ e=
      fun w : (Bool → (SwitchIndex d → Bool)) × (Card d → Bool) =>
        childLift (fun b => (butterflyPerm d (decodeButterfly d (w.1 b)))⁻¹)*pairSwitch w.2 := by
    funext w
    change (butterflyPerm (d+1) (decodeButterfly (d+1)
      ((coinStepEquiv d).symm ((w.1 false,w.1 true),w.2))))⁻¹=_
    rw [butterflyPerm_step,mul_inv_rev,childLift_inv,pairSwitch_inv]
    congr 2
    funext b
    cases b <;> rfl
  rw [←sampleOperator_equiv ρ _ e,he]
  exact sampleOperator_prod ρ
    (fun ω : Bool → (SwitchIndex d → Bool) => childLift (fun b => (butterflyPerm d (decodeButterfly d (ω b)))⁻¹))
    (pairSwitch (d := d))

end Thorp

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite DimensionEstimates Filter

lemma dimension_pos (μ : YoungDiagram) : 0 < Module.finrank ℂ (space μ) := by
  have h := factorial_le_dimension_row_column μ
  by_contra hn
  have hz : Module.finrank ℂ (space μ)=0 := by omega
  rw [hz,zero_mul,zero_mul] at h
  exact (Nat.factorial_pos μ.card).not_ge h

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

namespace Thorp.Specht
open scoped BigOperators Classical

lemma pair_sum_taboid_zero (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ)
    (hj : 2^d < μ.colLen 0) (v : space μ) :
    (∑ ξ : Card d → Bool, tabloidRep μ (e.permCongr (pairSwitch ξ))) v.1=0 := by
  have he : (∑ ξ : Card d → Bool, tabloidRep μ (e.permCongr (pairSwitch ξ)))=
      symmetrizer (fiberGroup (fun x => Fin.tail (e.symm x))) (tabloidRep μ) :=
    Fintype.sum_equiv (pairFiberEquiv d μ e) _ _ (fun _ => rfl)
  rw [he]
  exact tall_column_average_zero μ _ 0 (by simpa only [card_positions] using hj) v.1 v.2

lemma pair_operator_tall_zero (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ)
    (hj : 2^d < μ.colLen 0) :
    UnitaryFinite.sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) pairSwitch=0 := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (spaceHilbertEquiv μ).surjective v
  have hh : (∑ ξ : Card d → Bool, representation μ (e.permCongr (pairSwitch ξ))) w=0 := by
    apply Subtype.ext
    simp only [LinearMap.sum_apply,Submodule.coe_sum,Submodule.coe_zero]
    change (∑ ξ : Card d → Bool, tabloidRep μ (e.permCongr (pairSwitch ξ)) w.1)=0
    simpa only [LinearMap.sum_apply] using pair_sum_taboid_zero d μ e hj w
  have hh' := congrArg (spaceHilbertEquiv μ) hh
  simp only [LinearMap.sum_apply,map_sum,map_zero] at hh'
  change ((Fintype.card (Card d → Bool):ℂ)⁻¹ •
    ∑ ξ : Card d → Bool, UnitaryFinite.continuousRepresentation (relabelledUnitary μ e) (pairSwitch ξ))
      (spaceHilbertEquiv μ w)=0
  rw [smul_apply,sum_apply]
  change (Fintype.card (Card d → Bool):ℂ)⁻¹ •
    (∑ ξ : Card d → Bool, spaceHilbertEquiv μ (representation μ (e.permCongr (pairSwitch ξ))
      ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ w))))=0
  simp only [LinearEquiv.symm_apply_apply,hh',smul_zero]

open UnitaryFinite

lemma palindrome_tall_zero (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ)
    (hj : 2^d<μ.colLen 0) :
    sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm (d+1))=0 := by
  let ρ := relabelledUnitary μ e
  let : NormedAddCommGroup (hilbertSpace μ) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance
  have hpair : sampleOperator (V := hilbertSpace μ) ρ (pairSwitch (d := d))=0 := pair_operator_tall_zero d μ e hj
  have hi : sampleOperator ρ (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹)=0 := by
    rw [inverse_butterfly_average_step,hpair,mul_zero]
  rw [sampleOperator_inv ρ (relabelledUnitary_unitary μ e)] at hi
  rw [sampleOperator_palindrome _ _ (relabelledUnitary_unitary μ e),hi,mul_zero]

lemma palindrome_tall_zero_general (d : ℕ) (hd : 0<d) (μ : YoungDiagram) (e : Card d ≃ Cell μ)
    (hj : (μ.card:ℝ)/2<(μ.colLen 0:ℝ)) :
    sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)=0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  apply palindrome_tall_zero r μ e
  have hc : μ.card=2^(r+1) := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  rw [hc,Nat.cast_pow,Nat.cast_ofNat,pow_succ] at hj
  have hh : (2:ℝ)^r<(μ.colLen 0:ℝ) := by linarith
  exact_mod_cast hh

end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_TupleKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.Casimir
open scoped BigOperators Classical

section
open UnitaryFinite

lemma K_norm_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    ‖K d μ e‖ ≤ 1 :=
  sampleOperator_norm_le _ (Specht.relabelledUnitary_unitary μ e) _

lemma levelScale_ge (n k : ℕ) (hk : k ≤ n) : (k:ℝ) ≤ levelScale n k := by
  by_cases h : k=0
  · simp [h,levelScale]
  have hkp : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero h
  have hlog : 0 ≤ Real.log ((n:ℝ)/k) := Real.log_nonneg ((one_le_div hkp).mpr (by exact_mod_cast hk))
  dsimp [levelScale]
  nlinarith

end
open Filter UnitaryFinite DimensionEstimates

lemma levelScale_le (n k : ℕ) (hn : 0<n) (_hk : k≤n) : levelScale n k ≤ n := by
  by_cases hz : k=0
  · simp [hz,levelScale]
  have hkp : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hh := Real.log_le_sub_one_of_pos (div_pos hnp hkp)
  have hm := mul_le_mul_of_nonneg_left hh hkp.le
  have he : (k:ℝ)*((n:ℝ)/k)=n := mul_div_cancel₀ _ (ne_of_gt hkp)
  dsimp [levelScale]
  nlinarith

lemma nontrivial_uniform_zero (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : 0<μ.card-μ.rowLen 0) :
    uniformOperator (V:=Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e)=0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply SparseContact.point_relabelled_fixed_zero μ e ∅ (by simpa using hk)
  intro g _
  have he := congrArg (fun A : Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ => A v)
    (uniformOperator_left (V:=Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e) g)
  exact he

lemma gap_of_uniform_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) (hz : uniformOperator ρ=0) :
    ‖sampleOperator ρ (palindromePerm d)‖ ≤ blockGap d := by
  have hh := palindrome_off_invariants_gap d ρ hρ
  rw [hz,sub_zero,←sampleOperator_weighted] at hh
  exact hh

lemma nontrivial_gap (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : 0<μ.card-μ.rowLen 0) : ‖K d μ e‖ ≤ blockGap d := by
  exact gap_of_uniform_zero (V:=Specht.hilbertSpace μ) d _
    (Specht.relabelledUnitary_unitary μ e) (nontrivial_uniform_zero d μ e hk)

lemma finite_positive_lower (f : ℕ → ℝ) (D : ℕ) (hf : ∀ d<D,0<f d) :
    ∃ b : ℝ, 0<b ∧ ∀ d<D,b≤f d := by
  induction D with
  | zero => exact ⟨1,by norm_num,by omega⟩
  | succ D ih =>
    obtain ⟨b,hb,hh⟩ := ih (fun d hd => hf d (by omega))
    refine ⟨min b (f D),lt_min hb (hf D (by omega)),?_⟩
    intro d hd
    by_cases he : d=D
    · subst d; exact min_le_right _ _
    · exact (min_le_left _ _).trans (hh d (by omega))

theorem level_contraction :
    ∃ a : ℝ, 0<a ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0<μ.card-μ.rowLen 0 →
        ‖K d μ e‖ ≤ Real.exp (-a*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  obtain ⟨a,ha,he⟩ := eventual_level_contraction_q77
  obtain ⟨D,hD⟩ := eventually_atTop.mp he
  let f (d : ℕ) : ℝ := -Real.log (blockGap d)/(2:ℝ)^d
  have hf (d : ℕ) : 0<f d := by
    have hl := Real.log_neg (blockGap_pos d) (blockGap_lt_one d)
    exact div_pos (neg_pos.mpr hl) (by positivity)
  obtain ⟨b,hb,hbD⟩ := finite_positive_lower f D (fun d _ => hf d)
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro d μ e hk
  have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hkn : μ.card-μ.rowLen 0≤2^d := by omega
  have hΛ : 0≤levelScale (2^d) (μ.card-μ.rowLen 0) :=
    (Nat.cast_nonneg _).trans (levelScale_ge _ _ hkn)
  by_cases hd : D≤d
  · apply (hD d hd μ e hk).trans (Real.exp_le_exp.mpr _)
    have hh := mul_le_mul_of_nonneg_right (min_le_left a b) hΛ
    linarith
  · have hab : min a b≤f d := (min_le_right _ _).trans (hbD d (by omega))
    have hscale : levelScale (2^d) (μ.card-μ.rowLen 0) ≤ (2:ℝ)^d := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using levelScale_le (2^d) _ (by positivity) hkn
    have hprod := mul_le_mul_of_nonneg_right hab (by positivity : (0:ℝ)≤(2:ℝ)^d)
    have hfprod : f d*(2:ℝ)^d = -Real.log (blockGap d) := by dsimp [f]; field_simp
    rw [hfprod] at hprod
    have hs := mul_le_mul_of_nonneg_left hscale (le_of_lt (lt_min ha hb))
    calc
      _ ≤ blockGap d := nontrivial_gap d μ e hk
      _ = Real.exp (Real.log (blockGap d)) := (Real.exp_log (blockGap_pos d)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Thorp.Casimir

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht UnitaryFinite

lemma dimension_le_factorial (μ : YoungDiagram) :
    Module.finrank ℂ (space μ) ≤ μ.card.factorial := by
  have hdim : Module.finrank ℂ (space μ) ≤ Fintype.card (Tabloid μ) := by
    simpa using Submodule.finrank_le (space μ)
  have hrow : 1 ≤ Fintype.card (rowGroup μ) := Fintype.card_pos
  have hc := card_tabloid_mul_row μ
  nlinarith

lemma sweep_sq_palindrome (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ) (rev : Bool) :
    ‖SparseContact.sweepOperator d μ e rev‖^2 =
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ := by
  rw [SparseContact.sweep_forward_norm, sampleOperator_palindrome _ _ (relabelledUnitary_unitary μ e)]
  change ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))‖^2 = _
  rw [show (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint =
    star (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))) from rfl]
  simpa only [pow_two] using (CStarRing.norm_self_mul_star (x := sampleOperator (V := hilbertSpace μ)
    (relabelledUnitary μ e) (fun ω => butterflyPerm d (decodeButterfly d ω)))).symm

end Thorp.StrongTail

namespace Thorp.Harmonic
open scoped BigOperators Classical

open Filter _root_.OAI.ThorpNine.Adaptive.Thorp.Casimir

lemma dimension_contraction :
    ∃ b : ℝ, 0<b ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0<μ.card-μ.rowLen 0 →
      W d μ e ≤ Real.exp (-b*Real.log (Module.finrank ℂ (Specht.space μ):ℝ)) := by
  obtain ⟨a,h,ha,hh,he⟩ := Specht.spectral_regimes_q77
  obtain ⟨D,hD⟩ := eventually_atTop.mp (he.and (eventually_ge_atTop 1))
  let B (d : ℕ) : ℝ := 1+Real.log ((2^d).factorial:ℝ)
  have hB (d : ℕ) : 0<B d := by
    have hh : 0≤Real.log ((2^d).factorial:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (2^d))
    dsimp [B]; linarith
  let f (d : ℕ) : ℝ := -Real.log (blockGap d)/B d
  have hf (d : ℕ) : 0<f d :=
    div_pos (neg_pos.mpr (Real.log_neg (blockGap_pos d) (blockGap_lt_one d))) (hB d)
  obtain ⟨b,hb,hbD⟩ := finite_positive_lower f D (fun d _ => hf d)
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro d μ e hk
  have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hDpos : (0:ℝ)<Module.finrank ℂ (Specht.space μ) := by exact_mod_cast Specht.dimension_pos μ
  have hL : 0≤Real.log (Module.finrank ℂ (Specht.space μ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast Specht.dimension_pos μ)
  by_cases hd : D≤d
  · obtain ⟨hs,hd1⟩ := hD d hd
    by_cases ht : (μ.card:ℝ)/2<μ.colLen 0
    · have hz := Specht.palindrome_tall_zero_general d (by omega) μ e ht
      change K d μ e=0 at hz
      change ‖K d μ e‖≤_
      rw [hz,@norm_zero (Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ) _]
      exact (Real.exp_pos _).le
    · apply (hs μ e hk (le_of_not_gt ht)).1.trans
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (min_le_left a b) hL
      linarith
  · have hdim : Real.log (Module.finrank ℂ (Specht.space μ):ℝ) ≤ B d := by
      have hh := StrongTail.dimension_le_factorial μ
      rw [hμ] at hh
      have hl := Real.log_le_log hDpos (show (Module.finrank ℂ (Specht.space μ):ℝ)≤(2^d).factorial by exact_mod_cast hh)
      dsimp [B]; linarith
    have hab : min a b≤f d := (min_le_right _ _).trans (hbD d (by omega))
    have hp := mul_le_mul_of_nonneg_right hab (hB d).le
    have heq : f d*B d = -Real.log (blockGap d) := by dsimp [f]; field_simp [ne_of_gt (hB d)]
    rw [heq] at hp
    have hscale := mul_le_mul_of_nonneg_left hdim (le_of_lt (lt_min ha hb))
    calc
      W d μ e ≤ blockGap d := nontrivial_gap d μ e hk
      _ = Real.exp (Real.log (blockGap d)) := (Real.exp_log (blockGap_pos d)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma exp_intersection {x A B : ℝ} (hx : 0≤x) (hA : x≤Real.exp A) (hB : x≤Real.exp B) :
    x≤Real.exp ((A+B)/2) := by
  have hh := mul_le_mul hA hB hx (Real.exp_pos A).le
  rw [←Real.exp_add] at hh
  have he : Real.exp ((A+B)/2)^2=Real.exp (A+B) := by
    rw [pow_two,←Real.exp_add]
    congr 1; ring
  nlinarith [Real.exp_pos ((A+B)/2)]

end Thorp.Harmonic


namespace Thorp.AdaptiveBounds
open scoped BigOperators Classical

lemma familyBound_pos : 0<familyBound := by
  have hh : Real.exp (-(1:ℝ)/64)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold familyBound
  positivity

lemma densityConstant_pos : 0<densityConstant := by
  dsimp [densityConstant]
  linarith [familyBound_pos]

end Thorp.AdaptiveBounds

namespace Thorp.AdaptiveBounds
open scoped BigOperators Classical

section
open _root_.OAI.ThorpNine.Adaptive.Thorp.Casimir UnitaryFinite

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma positiveSquare_norm (T : V →L[ℂ] V) : ‖positiveSquare T‖=‖T‖^2 := by
  change ‖T*star T‖=‖T‖^2
  simpa only [pow_two] using CStarRing.norm_self_mul_star (x:=T)

omit [FiniteDimensional ℂ V] in
lemma trace_mul_fourth_comm (A B : V →L[ℂ] V) :
    LinearMap.trace ℂ V ((A*B)^4).toLinearMap =
      LinearMap.trace ℂ V ((B*A)^4).toLinearMap := by
  change LinearMap.trace ℂ V ((A.toLinearMap*B.toLinearMap)^4) =
    LinearMap.trace ℂ V ((B.toLinearMap*A.toLinearMap)^4)
  rw [show (A.toLinearMap*B.toLinearMap)^4=
    (A.toLinearMap*(B.toLinearMap*A.toLinearMap)^3)*B.toLinearMap by noncomm_ring]
  rw [LinearMap.trace_mul_comm]
  congr 1

lemma F_norm (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖F d μ e rev‖=‖K d μ e‖ := by
  change ‖positiveSquare (V:=Specht.hilbertSpace μ) (SparseContact.sweepOperator d μ e rev)‖=_
  rw [positiveSquare_norm]
  exact StrongTail.sweep_sq_palindrome d μ e rev

lemma F_false (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) : F d μ e false=K d μ e := by
  simp only [F,positiveSquare,SparseContact.sweepOperator]
  exact (sampleOperator_palindrome _ _ (Specht.relabelledUnitary_unitary μ e)).symm

lemma trace_eq (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    fourthTrace d μ e rev=traceMoment d μ e 4 := by
  cases rev with
  | false => rw [fourthTrace,F_false]; rfl
  | true =>
    unfold fourthTrace traceMoment
    rw [←F_false]
    simp only [F,positiveSquare,SparseContact.sweepOperator,ite_true]
    rw [sampleOperator_inv _ (Specht.relabelledUnitary_unitary μ e),ContinuousLinearMap.adjoint_adjoint]
    congr 1
    exact trace_mul_fourth_comm (V:=Specht.hilbertSpace μ) _ _

lemma fourthTrace_bound (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    fourthTrace d μ e rev≤Real.exp (-Real.log (Module.finrank ℂ (Specht.space μ):ℝ)+
      (1+3*densityConstant)*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  rw [trace_eq]
  let D : ℝ := Module.finrank ℂ (Specht.space μ)
  have hD : 0<D := by
    dsimp [D]
    exact_mod_cast Specht.dimension_pos μ
  have hh:=dimension_trace_bound_q77 d μ e
  have he : Real.exp (-Real.log D+(1+3*densityConstant)*levelScale (2^d) (μ.card-μ.rowLen 0))=
      Real.exp ((1+3*densityConstant)*levelScale (2^d) (μ.card-μ.rowLen 0))/D := by
    rw [Real.exp_add,Real.exp_neg,Real.exp_log hD]
    ring
  change _≤Real.exp (-Real.log D+_)
  rw [he]
  apply (le_div_iff₀ hD).mpr
  simpa only [mul_comm] using hh

lemma zero_level_dimension (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : μ.card-μ.rowLen 0=0) : Module.finrank ℂ (Specht.space μ)=1 := by
  have hr : μ.rowLen 0=μ.card := by have hh:=Specht.rowLen_zero_le_card μ; omega
  have hnp : 0<μ.card := by
    rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
    positivity
  have hcol : 0<μ.colLen 0 := by
    have hh : (0,0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact YoungDiagram.mem_iff_lt_colLen.mp hh
  have hg : μ.card.factorial ≤ Fintype.card (Specht.rowGroup μ) := by
    rw [Specht.card_rowGroup,←hr]
    simpa using (Finset.single_le_prod' (f := fun i : Fin (μ.colLen 0) => (μ.rowLen i).factorial)
      (s := Finset.univ) (fun i _ => Nat.factorial_pos (μ.rowLen i))
      (Finset.mem_univ (⟨0,hcol⟩ : Fin (μ.colLen 0))))
  have hc := Specht.card_tabloid_mul_row μ
  have hD : Module.finrank ℂ (Specht.space μ) ≤ Fintype.card (Specht.Tabloid μ) := by
    simpa using Submodule.finrank_le (Specht.space μ)
  have hp := Specht.dimension_pos μ
  have hf := Nat.factorial_pos μ.card
  nlinarith

end
open _root_.OAI.ThorpNine.Adaptive.Thorp.Casimir

theorem adaptive_main_q77_oai : MainStatement := by
  obtain ⟨a,ha,hlevel⟩ := level_contraction
  obtain ⟨b,hb,hdim⟩ := Harmonic.dimension_contraction
  refine ⟨a,1,1+3*densityConstant,min a b/4,ha,by norm_num,
    by linarith [densityConstant_pos],by positivity,?_⟩
  intro d μ e rev
  dsimp only
  let L := levelScale (2^d) (μ.card-μ.rowLen 0)
  let D : ℝ := Module.finrank ℂ (Specht.space μ)
  have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hL : 0≤L := (Nat.cast_nonneg (μ.card-μ.rowLen 0)).trans
    (levelScale_ge (2^d) _ (by omega))
  have hD : 0≤Real.log D := Real.log_nonneg (by
    dsimp [D]
    exact_mod_cast Specht.dimension_pos μ)
  refine ⟨?_,?_,?_⟩
  · rw [F_norm]
    by_cases hk : 0<μ.card-μ.rowLen 0
    · exact hlevel d μ e hk
    · have hz : μ.card-μ.rowLen 0=0 := by omega
      simpa only [hz,levelScale,Nat.cast_zero,zero_mul,mul_zero,Real.exp_zero] using
        K_norm_le_one d μ e
  · simpa only [neg_mul,one_mul] using fourthTrace_bound d μ e rev
  · by_cases hk : 0<μ.card-μ.rowLen 0
    · have hw := hlevel d μ e hk
      have hd := hdim d μ e hk
      change ‖K d μ e‖≤Real.exp (-a*L) at hw
      change ‖K d μ e‖≤Real.exp (-b*Real.log D) at hd
      have hg:=Harmonic.exp_intersection (norm_nonneg (K d μ e)) hw hd
      have hcoef : (-a*L+-b*Real.log D)/2 ≤ -2*(min a b/4)*(Real.log D+L) := by
        have h₁:=mul_le_mul_of_nonneg_right (min_le_left a b) hL
        have h₂:=mul_le_mul_of_nonneg_right (min_le_right a b) hD
        nlinarith
      have hg' :=hg.trans (Real.exp_le_exp.mpr hcoef)
      have hs :=StrongTail.sweep_sq_palindrome d μ e rev
      change ‖SparseContact.sweepOperator d μ e rev‖^2=‖K d μ e‖ at hs
      rw [←hs] at hg'
      have he : Real.exp (-(min a b/4)*(Real.log D+L))^2=
          Real.exp (-2*(min a b/4)*(Real.log D+L)) := by
        rw [pow_two,←Real.exp_add]
        congr 1; ring
      change ‖SparseContact.sweepOperator d μ e rev‖≤Real.exp (-(min a b/4)*(Real.log D+L))
      nlinarith [Real.exp_pos (-(min a b/4)*(Real.log D+L))]
    · have hz : μ.card-μ.rowLen 0=0 := by omega
      rw [zero_level_dimension d μ e hz]
      simpa only [hz,levelScale,Nat.cast_zero,Nat.cast_one,Real.log_one,zero_mul,
        add_zero,mul_zero,Real.exp_zero] using SparseContact.sweep_norm_le_one d μ e rev

end Thorp.AdaptiveBounds

end ThorpNine.Adaptive

end OAI
end

theorem solution : type_of% @OAI.ThorpNine.Adaptive.Thorp.AdaptiveBounds.adaptive_main_q77_oai := @OAI.ThorpNine.Adaptive.Thorp.AdaptiveBounds.adaptive_main_q77_oai
