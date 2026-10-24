-- Prove2me | solution 1 for OAI.ThorpNine.Harmonic.Thorp.LowPlanes.regular_trace_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:26:58.953571+00:00
-- url     : https://prove2.me/submissions/7e615e5c-3ae2-4377-9b73-cd4d6e80d8a4

import Mathlib
import Definitions.Def_CoordinateTrace
import Definitions.Def_OAIQWTNR000
import Theorems.Thm_OAI_ThorpNine_Harmonic_Thorp_Casimir_level_contraction
import Theorems.Thm_OAI_ThorpNine_Harmonic_Thorp_HarmonicBounds_dimension_contraction

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp

open scoped BigOperators
open Filter

lemma card_permutations (d : ℕ) : Fintype.card (Equiv.Perm (Card d)) = Nat.factorial (2 ^ d) := by
  rw [Fintype.card_perm, card_positions]

lemma distance_nonneg (d t : ℕ) : 0 ≤ distance d t := by
  unfold distance
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

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

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_SandwichShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

lemma childLift_inv (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    (childLift p)⁻¹ = childLift (fun b => (p b)⁻¹) := rfl

lemma pairSwitch_inv (d : ℕ) (ξ : Card d → Bool) : (pairSwitch ξ)⁻¹ = pairSwitch ξ := rfl

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_ModifiedReverseCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

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

theorem alternator_pairing (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v = pairing (polytabloid μ) v • polytabloid μ := by
  rw [alternator_rank_one_exact,alternator_base_pairing]


lemma polytabloid_mem_space (μ : YoungDiagram) : polytabloid μ ∈ space μ := by
  simpa using orbit_mem_space μ 1

lemma alternator_mem_invariant (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) (v : Tabloid μ → ℂ) (hv : v ∈ W) :
    alternator (colGroup μ) (tabloidRep μ) v ∈ W := by
  classical
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply]
  exact W.sum_mem (fun c _ => W.smul_mem _ (hW c v hv))

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

theorem space_simple (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) (hWS : W ≤ space μ) :
    W = ⊥ ∨ W = space μ := by
  obtain hSW | horth := submodule_theorem μ W hW
  · exact Or.inr (le_antisymm hWS hSW)
  · left
    apply le_antisymm _ bot_le
    intro v hv
    exact (pairing_self_eq_zero v).mp (horth v hv v (hWS hv))


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

end Symmetrizer

lemma swap_polytabloid {μ : YoungDiagram} (x y : Cell μ) (hne : x ≠ y)
    (hcol : col x = col y) :
    tabloidRep μ (Equiv.swap x y) (polytabloid μ) = -polytabloid μ := by
  have h := action_alternator_apply (colGroup μ) (tabloidRep μ)
    ⟨Equiv.swap x y,swap_mem_colGroup x y hcol⟩ (delta (baseTabloid μ))
  simpa only [polytabloid,permSign_swap hne,neg_one_smul] using h

lemma eq_of_row_preserving (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (he : ∀ x, row (e x) = row x) : μ = ν := by
  have hlen (i : ℕ) : μ.rowLen i = ν.rowLen i := by
    let ei : {x : Cell μ // row x = i} ≃ {x : Cell ν // row x = i} :=
      { toFun := fun x => ⟨e x.1,(he x.1).trans x.2⟩
        invFun := fun x => ⟨e.symm x.1,by
          have h := he (e.symm x.1)
          simp only [Equiv.apply_symm_apply] at h
          exact h.symm.trans x.2⟩
        left_inv := fun x => by apply Subtype.ext; exact e.symm_apply_apply _
        right_inv := fun x => by apply Subtype.ext; exact e.apply_symm_apply _ }
    simpa only [Fintype.card_fin] using Fintype.card_congr
      ((rowEquiv μ i).symm.trans (ei.trans (rowEquiv ν i)))
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen,hlen]

lemma column_injective_rowCost (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (h : ∀ x y : Cell μ, col x = col y → row (e x) = row (e y) → x = y) :
    rowCost μ ≤ rowCost ν ∧ (rowCost μ = rowCost ν → μ = ν) := by
  let c := rankPerm (fun x => row (e x)) h
  have hle (x : Cell μ) : row (c x) ≤ row (e x) := rankCell_row_le _ h x
  have hsumc : ∑ x, row (c x) = rowCost μ := Equiv.sum_comp c _
  have hsume : ∑ x, row (e x) = rowCost ν := Equiv.sum_comp e _
  constructor
  · rw [←hsumc,←hsume]
    exact Finset.sum_le_sum (fun x _ => hle x)
  · intro heq
    have he : ∀ x, row (c x) = row (e x) := by
      apply fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).mp
        (hsumc.trans (heq.trans hsume.symm)) x (Finset.mem_univ _)
    apply eq_of_row_preserving μ ν (c.symm.trans e)
    intro x
    simpa using (he (c.symm x)).symm

lemma swap_relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (x y : α) : e.permCongr (Equiv.swap x y) = Equiv.swap (e x) (e y) := by
  ext z
  simp only [Equiv.permCongr_apply]
  exact e.injective.map_swap x y (e.symm z) |>.trans (by simp)

lemma sign_vector_rowCost (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (v : Tabloid ν → ℂ) (hv : v ≠ 0)
    (hs : ∀ c : colGroup μ,
      tabloidRep ν (e.permCongr c) v = permSign (c : Equiv.Perm (Cell μ)) • v) :
    rowCost μ ≤ rowCost ν ∧ (rowCost μ = rowCost ν → μ = ν) := by
  obtain ⟨f,hf⟩ : ∃ f, v f ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨p,hp⟩ := f.2
  apply column_injective_rowCost μ ν (e.trans p)
  intro x y hcol hrow
  by_contra hne
  have hfix : tabloidAct (Equiv.swap (e x) (e y)) f = f := by
    apply swap_fixes_tabloid
    rw [hp]
    exact Fin.ext hrow
  have heq := congrArg (fun w : Tabloid ν → ℂ => w f)
    (hs ⟨Equiv.swap x y,swap_mem_colGroup x y hcol⟩)
  rw [swap_relabel,permSign_swap hne] at heq
  simp only [tabloidRep_apply,Equiv.swap_inv,hfix,Pi.smul_apply,neg_one_smul] at heq
  apply hf
  have h2 : (2:ℂ)*(v f) = 0 := by linear_combination heq
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

lemma polytabloid_col_action (μ : YoungDiagram) (c : colGroup μ) :
    tabloidRep μ c (polytabloid μ) = permSign (c:Equiv.Perm (Cell μ)) • polytabloid μ :=
  action_alternator_apply _ _ c _

theorem shapes_eq_of_equivariant_equiv (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (T : space μ ≃ₗ[ℂ] space ν)
    (hT : ∀ p v, T (representation μ p v) = representation ν (e.permCongr p) (T v)) :
    μ = ν := by
  let u : space μ := ⟨polytabloid μ,polytabloid_mem_space μ⟩
  have hu : u ≠ 0 := fun h => polytabloid_ne_zero μ (congrArg Subtype.val h)
  have hTcol (c : colGroup μ) :
      tabloidRep ν (e.permCongr c) (T u) = permSign (c:Equiv.Perm (Cell μ)) • (T u : Tabloid ν → ℂ) := by
    change (representation ν (e.permCongr c) (T u) : Tabloid ν → ℂ) = _
    rw [←hT]
    have hh : representation μ c u = permSign (c:Equiv.Perm (Cell μ)) • u :=
      Subtype.ext (polytabloid_col_action μ c)
    rw [hh,map_smul]
    rfl
  have hfwd := sign_vector_rowCost μ ν e (T u)
    (fun h => hu (T.injective (by apply Subtype.ext; simpa using h))) hTcol
  let w : space ν := ⟨polytabloid ν,polytabloid_mem_space ν⟩
  have hw : w ≠ 0 := fun h => polytabloid_ne_zero ν (congrArg Subtype.val h)
  have hTi (p : Equiv.Perm (Cell ν)) (v : space ν) :
      T.symm (representation ν p v) = representation μ (e.symm.permCongr p) (T.symm v) := by
    apply T.injective
    rw [T.apply_symm_apply,hT,T.apply_symm_apply]
    have hp : e.permCongr (e.symm.permCongr p) = p := by
      apply Equiv.ext
      intro x
      simp [Equiv.permCongr_apply]
    rw [hp]
  have hTicol (c : colGroup ν) :
      tabloidRep μ (e.symm.permCongr c) (T.symm w) =
        permSign (c:Equiv.Perm (Cell ν)) • (T.symm w : Tabloid μ → ℂ) := by
    change (representation μ (e.symm.permCongr c) (T.symm w) : Tabloid μ → ℂ) = _
    rw [←hTi]
    have hh : representation ν c w = permSign (c:Equiv.Perm (Cell ν)) • w :=
      Subtype.ext (polytabloid_col_action ν c)
    rw [hh,map_smul]
    rfl
  have hbwd := sign_vector_rowCost ν μ e.symm (T.symm w)
    (fun h => hw (T.symm.injective (by apply Subtype.ext; simpa using h))) hTicol
  exact hfwd.2 (Nat.le_antisymm hfwd.1 hbwd.1)


end Thorp.Specht

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_Shapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Specht
open scoped BigOperators Classical

lemma conjugacyPartition_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (conjugacyPartition (α := α)) := by
  intro p q
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      intro h
      exact Quotient.sound ((Equiv.Perm.partition_eq_of_isConj).mpr h)

end Thorp.Specht

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


end Thorp.Specht

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_AverageMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

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

lemma uniformOperator_left (ρ : Representation ℂ G V) (g : G) :
    continuousRepresentation ρ g * uniformOperator ρ=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

end
open scoped BigOperators Classical

end Thorp.UnitaryFinite

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

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

omit [Fintype G] in
lemma sampleOperator_one [Nonempty Ω] (ρ : Representation ℂ G V) :
    sampleOperator ρ (fun _ : Ω => 1)=1 := by
  simp only [sampleOperator,map_one,Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

end Thorp.UnitaryFinite

namespace Thorp.FiniteFourier
open scoped BigOperators ComplexConjugate Classical
open UnitaryFinite
variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hρ : ∀ i, IsUnitary (ρ i))
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)


lemma coefficientBasis_apply (a : CoefficientIndex V) :
    coefficientBasis V ρ hρ hneq hcard a=coefficientFamily V ρ a := congrFun (OrthonormalBasis.coe_mk _ _) a

include hρ hneq hcard in

theorem parseval (f : EuclideanSpace ℂ G) :
    ∑ a : CoefficientIndex V, ‖inner ℂ (coefficientFamily V ρ a) f‖^2=‖f‖^2 := by
  simpa only [coefficientBasis_apply] using
    (coefficientBasis V ρ hρ hneq hcard).sum_sq_norm_inner_right f


omit [Fintype ι] [∀ i, Representation.IsIrreducible (ρ i)] in
lemma coefficient_realVector (p : G → ℝ) (a : CoefficientIndex V) :
    inner ℂ (coefficientFamily V ρ a) (realVector p)=
      (Real.sqrt ((Module.finrank ℂ (V a.1):ℝ)/(Fintype.card G:ℝ)):ℂ)*
      inner ℂ (stdOrthonormalBasis ℂ (V a.1) a.2.2)
        (weightedOperator (ρ a.1) p (stdOrthonormalBasis ℂ (V a.1) a.2.1)) := by
  simp only [PiLp.inner_apply,coefficientFamily,regularCoefficient_apply,realVector,
    RCLike.inner_apply,map_mul,Complex.conj_ofReal,inner_conj_symm,
    weightedOperator,sum_apply,smul_apply,
    continuousRepresentation_apply,inner_sum,inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

omit [Fintype ι] [∀ i, Representation.IsIrreducible (ρ i)] in
lemma coefficient_realVector_sq (p : G → ℝ) (a : CoefficientIndex V) :
    ‖inner ℂ (coefficientFamily V ρ a) (realVector p)‖^2=
      ((Module.finrank ℂ (V a.1):ℝ)/(Fintype.card G:ℝ))*
      ‖inner ℂ (stdOrthonormalBasis ℂ (V a.1) a.2.2)
        (weightedOperator (ρ a.1) p (stdOrthonormalBasis ℂ (V a.1) a.2.1))‖^2 := by
  rw [coefficient_realVector,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

include hρ hneq hcard in
lemma parseval_operator (p : G → ℝ) :
    (Fintype.card G:ℝ)*‖realVector p‖^2=
      ∑ i,(Module.finrank ℂ (V i):ℝ)*∑ a : Fin (Module.finrank ℂ (V i)),
        ‖weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a)‖^2 := by
  rw [←parseval V ρ hρ hneq hcard (realVector p)]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,coefficient_realVector_sq]
  have hN : (Fintype.card G:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he (a : Fin (Module.finrank ℂ (V i))) :
      (∑ b : Fin (Module.finrank ℂ (V i)),
        (Module.finrank ℂ (V i):ℝ)/(Fintype.card G:ℝ)*
          ‖inner ℂ (stdOrthonormalBasis ℂ (V i) b)
            (weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a))‖^2)=
        (Module.finrank ℂ (V i):ℝ)/(Fintype.card G:ℝ)*
          ‖weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a)‖^2 := by
    rw [←Finset.mul_sum,(stdOrthonormalBasis ℂ (V i)).sum_sq_norm_inner_right]
  simp_rw [he]
  rw [←Finset.mul_sum]
  field_simp

include hρ hneq hcard in
lemma realVector_bound (p : G → ℝ) :
    (Fintype.card G:ℝ)*‖realVector p‖^2≤
      ∑ i,(Module.finrank ℂ (V i):ℝ)^2*‖weightedOperator (ρ i) p‖^2 := by
  rw [parseval_operator V ρ hρ hneq hcard]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ (Module.finrank ℂ (V i):ℝ)*∑ _a : Fin (Module.finrank ℂ (V i)),‖weightedOperator (ρ i) p‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [(stdOrthonormalBasis ℂ (V i)).norm_eq_one,mul_one] using
        (weightedOperator (ρ i) p).le_opNorm (stdOrthonormalBasis ℂ (V i) a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

include hρ hneq hcard in

theorem l1_fourier_bound (p : G → ℝ) :
    (∑ g,|p g|)^2≤∑ i,(Module.finrank ℂ (V i):ℝ)^2*‖weightedOperator (ρ i) p‖^2 := by
  apply le_trans _ (realVector_bound V ρ hρ hneq hcard p)
  have he : ‖realVector p‖^2=∑ g,|p g|^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [realVector,PiLp.toLp_apply,Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun g => |p g|)

end Thorp.FiniteFourier

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_PairAssembleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

lemma irreducible_of_equiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : Representation.Equiv ρ σ) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible σ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hi := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let f : ρ.asModule →ₗ[MonoidAlgebra ℂ G] σ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  have hf : Function.Bijective f := e.toLinearEquiv.bijective
  exact (f.isSimpleModule_iff_of_bijective hf).mp hi

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

lemma unitaryRepresentation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (unitaryRepresentation μ) := by
  let := representation_irreducible μ
  exact UnitaryFinite.irreducible_of_equiv _ _ (unitaryEquiv μ)

lemma unitaryRepresentation_unitary (μ : YoungDiagram) :
    UnitaryFinite.IsUnitary (G := Equiv.Perm (Cell μ)) (V := hilbertSpace μ) (unitaryRepresentation μ) := by
  intro p v w
  change inner ℂ (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ))
      (unitaryRepresentation μ p w : PermutationHilbert.H (Tabloid μ)) = _
  rw [unitaryRepresentation_coe,unitaryRepresentation_coe]
  exact (PermutationHilbert.act (tabloidAct p)).inner_map_map v w


end Thorp.Specht
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H X Ω : Type*} [Group G] [Group H] [Fintype G] [Fintype X] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [Fintype X] [Fintype Ω] [FiniteDimensional ℂ V] in
lemma irreducible_comp_equiv (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (e : H ≃* G) : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  exact (subrepresentationEquiv ρ e).isSimpleOrder_iff.mpr inferInstance

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma relabelledUnitary_unitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    UnitaryFinite.IsUnitary (V := hilbertSpace μ) (relabelledUnitary μ e) := by
  intro g v w
  exact unitaryRepresentation_unitary μ (e.permCongr g) v w

omit [Fintype α] in
lemma relabelledUnitary_irreducible (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation.IsIrreducible (relabelledUnitary μ e) := by
  let := unitaryRepresentation_irreducible μ
  exact UnitaryFinite.irreducible_comp_equiv (V := hilbertSpace μ) (unitaryRepresentation μ) e.permCongrHom

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

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_InsertionPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators Classical

lemma insertNth_castSucc_snoc {α : Type*} {d : ℕ} (i : Fin (d+1)) (b a : α) (y : Fin d → α) :
    Fin.insertNth i.castSucc b (Fin.snoc (α := fun _ => α) y a)=Fin.snoc (α := fun _ => α) (Fin.insertNth i b y) a := by
  apply Fin.lastCases ?_ (fun j => ?_) |> fun h => funext h
  · rw [←show i.castSucc.succAbove (Fin.last d)=Fin.last (d+1) from
        Fin.succAbove_castSucc_of_le i (Fin.last d) (Fin.le_last i),Fin.insertNth_apply_succAbove]
    simp
  · cases j using Fin.succAboveCases i with
    | x => simp
    | p j =>
      have he : i.castSucc.succAbove j.castSucc=(i.succAbove j).castSucc := by
        simp only [Fin.succAbove,Fin.castSucc_lt_castSucc_iff]
        split_ifs <;> rfl
      rw [←he,Fin.insertNth_apply_succAbove]
      simp

lemma rotate_cons (d : ℕ) (b : Bool) (y : Card d) :
    rotate (d+1) (Fin.cons b y)=Fin.snoc y b := (Fin.snoc_eq_cons_rotate y b).symm

lemma rotate_insert (d : ℕ) (i : Fin (d+1)) (b : Bool) (y : Card (d+1)) :
    rotate (d+2) (Fin.insertNth i.succ b y)=Fin.insertNth i.castSucc b (rotate (d+1) y) := by
  rw [←Fin.cons_self_tail y,Fin.insertNth_succ_cons,rotate_cons,rotate_cons,insertNth_castSucc_snoc]

lemma insertionPerm_apply (d : ℕ) (i : Fin (d+1)) (x : Card (d+1)) :
    insertionPerm d i x=Fin.insertNth i (x 0) (Fin.tail x) := rfl

lemma insertionPerm_zero (d : ℕ) : insertionPerm d 0=1 := by
  ext x j
  simp [insertionPerm_apply]

lemma insertionPerm_last (d : ℕ) : insertionPerm d (Fin.last d)=rotate (d+1) := by
  apply Equiv.ext
  intro x
  rw [insertionPerm_apply,Fin.insertNth_last',←rotate_cons,Fin.cons_self_tail]

lemma physical_carry_step (d : ℕ) (i : Fin (d+1)) (ξ : Bool → Coins (d+1)) :
    step (d+2) (fun y => ξ (y i) (Fin.removeNth i y))*insertionPerm (d+1) i.succ=
      insertionPerm (d+1) i.castSucc*childLift (fun b => step (d+1) (ξ b)) := by
  apply Equiv.ext
  intro x
  have he : Fin.cons (Bool.xor ((Fin.tail x) 0) (ξ (x 0) (Fin.tail (Fin.tail x))))
      (Fin.insertNth i (x 0) (Fin.tail (Fin.tail x))) =
      (Fin.insertNth i.succ (x 0) (switchFun (ξ (x 0)) (Fin.tail x)) : Card (d+2)) := by
    simp only [switchFun,Fin.insertNth_succ_cons]
  have hs : switchFun (fun y => ξ (y i) (Fin.removeNth i y))
      (Fin.insertNth i.succ (x 0) (Fin.tail x)) =
      (Fin.insertNth i.succ (x 0) (switchFun (ξ (x 0)) (Fin.tail x)) : Card (d+2)) := by
    conv_lhs => rw [←Fin.cons_self_tail (Fin.tail x),Fin.insertNth_succ_cons]
    simp only [switchFun,Fin.cons_zero,Fin.tail_cons,Fin.insertNth_apply_same,Fin.removeNth_insertNth]
    exact he
  change rotate (d+2) (switchFun (fun y => ξ (y i) (Fin.removeNth i y))
      (Fin.insertNth i.succ (x 0) (Fin.tail x))) = _
  rw [hs,rotate_insert]
  rfl

end Thorp
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω : Type*} [Fintype Ω]

lemma sampleOperator_mul_const (ρ : Representation ℂ G V) (P : Ω → G) (g : G) :
    sampleOperator ρ (fun ω => P ω*g)=sampleOperator ρ P*continuousRepresentation ρ g := by
  simp only [sampleOperator,map_mul,Finset.sum_mul,smul_mul_assoc]

lemma sampleOperator_const_mul (ρ : Representation ℂ G V) (P : Ω → G) (g : G) :
    sampleOperator ρ (fun ω => g*P ω)=continuousRepresentation ρ g*sampleOperator ρ P := by
  simp only [sampleOperator,map_mul,Finset.mul_sum,mul_smul_comm]

lemma sampleOperator_run (d t : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    sampleOperator ρ (run d t)=(sampleOperator ρ (step d))^t := by
  induction t with
  | zero => exact sampleOperator_one ρ
  | succ t ih =>
    let e : Coins d × (Fin t → Coins d) ≃ (Fin (t+1) → Coins d) :=
      Fin.snocEquiv (fun _ => Coins d)
    have he : run d (t+1) ∘ e=fun w => step d w.1*run d t w.2 := by
      funext w
      simp only [Function.comp_apply,e,Fin.snocEquiv_apply,
        run,Fin.snoc_last,Fin.snoc_castSucc]
    rw [←sampleOperator_equiv ρ (run d (t+1)) e,he,sampleOperator_prod,ih,pow_succ']

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma physical_carry_average (d : ℕ) (i : Fin d)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    sampleOperator ρ (step (d+1))*continuousRepresentation ρ (insertionPerm d i.succ)=
      continuousRepresentation ρ (insertionPerm d i.castSucc)*
        sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b))) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    have he : (fun ξ : Bool → Coins (d+1) =>
        step (d+2) (carryCoins d i ξ)*insertionPerm (d+1) i.succ)=
      (fun ξ => insertionPerm (d+1) i.castSucc*childLift (fun b => step (d+1) (ξ b))) := by
      funext ξ
      exact physical_carry_step d i ξ
    have h := congrArg (sampleOperator ρ) he
    rw [sampleOperator_mul_const,sampleOperator_const_mul] at h
    change sampleOperator ρ (step (d+2) ∘ carryCoins d i)*_=_ at h
    rw [sampleOperator_equiv] at h
    exact h

theorem physical_sweep_recursion (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    (sampleOperator ρ (step (d+1)))^(d+1)=
      (sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b))))^d*
        sampleOperator ρ (pairSwitch (d := d)) := by
  let A := sampleOperator ρ (step (d+1))
  let K := sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b)))
  have h (t : ℕ) (ht : t≤d) : A^t*continuousRepresentation ρ (insertionPerm d ⟨t,by omega⟩)=K^t := by
    induction t with
    | zero =>
      change 1*continuousRepresentation ρ (insertionPerm d 0)=1
      rw [insertionPerm_zero,map_one,one_mul]
    | succ t ih =>
      have hc := physical_carry_average d (⟨t,by omega⟩ : Fin d) ρ
      change A*continuousRepresentation ρ (insertionPerm d ⟨t+1,by omega⟩)=
        continuousRepresentation ρ (insertionPerm d ⟨t,by omega⟩)*K at hc
      rw [pow_succ,mul_assoc,hc,←mul_assoc,ih (by omega),←pow_succ]
  have he : sampleOperator ρ (step (d+1))=
      continuousRepresentation ρ (rotate (d+1))*sampleOperator ρ (pairSwitch (d := d)) :=
    sampleOperator_const_mul ρ (pairSwitch (d := d)) (rotate (d+1))
  calc
    _ = A^d*A := pow_succ A d
    _ = A^d*(continuousRepresentation ρ (insertionPerm d (Fin.last d))*
        sampleOperator ρ (pairSwitch (d := d))) := by rw [insertionPerm_last]; rw [←he]
    _ = _ := by
      rw [←mul_assoc]
      exact congrArg (fun z => z*sampleOperator ρ (pairSwitch (d := d))) (h d le_rfl)

end Thorp
namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite

lemma childInjection_product (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    childInjection d false (p false)*childInjection d true (p true)=childLift p := by
  change childLift _*childLift _=_
  rw [childLift_mul]
  congr 1
  funext b
  cases b <;> simp

lemma childInjection_commute (d : ℕ) (p q : Equiv.Perm (Card d)) :
    Commute (childInjection d false p) (childInjection d true q) := by
  change childLift _*childLift _=childLift _*childLift _
  rw [childLift_mul,childLift_mul]
  congr 1
  funext b
  cases b <;> simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω : Type*} [Fintype Ω]

lemma sampleOperator_child (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V)
    (P : Ω → Equiv.Perm (Card d)) :
    sampleOperator ρ (fun ω : Bool → Ω => childLift (fun b => P (ω b)))=
      sampleOperator (ρ.comp (childInjection d false)) P*
        sampleOperator (ρ.comp (childInjection d true)) P := by
  let e := (Equiv.boolArrowEquivProd Ω).symm
  have he : (fun ω : Bool → Ω => childLift (fun b => P (ω b))) ∘ e=
      fun w : Ω × Ω => childInjection d false (P w.1)*childInjection d true (P w.2) := by
    funext w
    change childLift (fun b => P (e w b))=_
    rw [←childInjection_product]
    rfl
  rw [←sampleOperator_equiv ρ _ e,he]
  exact sampleOperator_prod ρ (fun w => childInjection d false (P w))
    (fun w => childInjection d true (P w))

lemma sampleOperator_child_commute (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V)
    (P : Ω → Equiv.Perm (Card d)) :
    Commute (sampleOperator (ρ.comp (childInjection d false)) P)
      (sampleOperator (ρ.comp (childInjection d true)) P) := by
  rw [sampleOperator_comp,sampleOperator_comp]
  exact sampleOperator_commute ρ _ _ (fun _ _ => childInjection_commute d _ _)

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

theorem physical_sweep_inverse_butterfly (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    (sampleOperator ρ (step d))^d=
      sampleOperator ρ (fun ω => (butterflyPerm d (decodeButterfly d ω))⁻¹) := by
  induction d with
  | zero =>
    symm
    exact sampleOperator_one ρ
  | succ d ih =>
    rw [physical_sweep_recursion,sampleOperator_child,
      (sampleOperator_child_commute d ρ (step d)).mul_pow,ih,ih,
      inverse_butterfly_average_step]
    rw [sampleOperator_child d ρ (fun ω => (butterflyPerm d (decodeButterfly d ω))⁻¹)]

lemma physical_sweep_adjoint (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) (hρ : IsUnitary ρ) :
    sampleOperator ρ (run d d)=
      (sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint := by
  rw [sampleOperator_run,physical_sweep_inverse_butterfly,sampleOperator_inv ρ hρ]

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


end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_TailShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Specht
open scoped BigOperators Classical

lemma partition_count (N : ℕ) : Fintype.card (Nat.Partition N)≤2^N := by
  have h := Fintype.card_le_of_surjective (Nat.Partition.ofComposition N) Nat.Partition.ofComposition_surj
  rw [composition_card] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le N 1))

lemma positive_list_eq_of_tail_sum {a b : List ℕ}
    (ha : ∀ x∈a, 0<x) (hb : ∀ x∈b, 0<x) (ht : a.tail=b.tail) (hs : a.sum=b.sum) : a=b := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x l =>
      simp only [List.tail_nil,List.tail_cons] at ht
      subst l
      have hx := hb x (by simp)
      simp only [List.sum_nil,List.sum_cons,add_zero] at hs
      omega
  | cons x l =>
    cases b with
    | nil =>
      simp only [List.tail_nil,List.tail_cons] at ht
      subst l
      have hx := ha x (by simp)
      simp only [List.sum_nil,List.sum_cons,add_zero] at hs
      omega
    | cons y m =>
      simp only [List.tail_cons] at ht
      subst m
      simp only [List.sum_cons] at hs
      congr 1
      omega

lemma tailShapePartition_injective (N j : ℕ) : Function.Injective (tailShapePartition N j) := by
  intro μ ν he
  have hh : (μ.1.1.rowLens.tail : Multiset ℕ)=(ν.1.1.rowLens.tail : Multiset ℕ) :=
    congrArg Nat.Partition.parts he
  have ht : μ.1.1.rowLens.tail=ν.1.1.rowLens.tail := by
    have hm := congrArg (fun s : Multiset ℕ => s.sort (· ≥ ·)) hh
    simpa only [Multiset.coe_sort,
      List.mergeSort_eq_self _ μ.1.1.rowLens_sorted.pairwise.tail,
      List.mergeSort_eq_self _ ν.1.1.rowLens_sorted.pairwise.tail] using hm
  have hl := positive_list_eq_of_tail_sum (μ.1.1.pos_of_mem_rowLens) (ν.1.1.pos_of_mem_rowLens)
    ht (by rw [sum_rowLens,sum_rowLens,μ.1.2,ν.1.2])
  apply Subtype.ext
  apply Subtype.ext
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext hl

lemma tail_shapes_count (N j : ℕ) : Fintype.card (TailShapes N j)≤2^j := by
  exact (Fintype.card_le_of_injective _ (tailShapePartition_injective N j)).trans (partition_count j)

end Thorp.Specht

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.Harmonic_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Casimir
open scoped BigOperators Classical
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

end Thorp.Casimir

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

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

end Thorp.Casimir

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite

lemma cardRepresentation_unitary (d : ℕ) (μ : Shapes (2^d)) :
    IsUnitary (V := hilbertSpace μ.1) (cardRepresentation d μ) :=
  relabelledUnitary_unitary _ _

noncomputable instance cardRepresentation_irreducible (d : ℕ) (μ : Shapes (2^d)) :
    Representation.IsIrreducible (cardRepresentation d μ) :=
  relabelledUnitary_irreducible _ _

lemma relabelledUnitary_neq {α : Type*} (μ ν : YoungDiagram)
    (e : α ≃ Cell μ) (f : α ≃ Cell ν)
    (T : Representation.Equiv (relabelledUnitary μ e) (relabelledUnitary ν f)) : μ=ν := by
  let S := (spaceHilbertEquiv μ).trans (T.toLinearEquiv.trans (spaceHilbertEquiv ν).symm)
  apply shapes_eq_of_equivariant_equiv μ ν (e.symm.trans f) S
  intro p v
  have hT := Representation.IntertwiningMap.isIntertwining _ _ T.toIntertwiningMap
    (e.symm.permCongr p) (spaceHilbertEquiv μ v)
  change T.toLinearEquiv (spaceHilbertEquiv μ
    (representation μ (e.permCongr (e.symm.permCongr p))
      ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v))))=
    spaceHilbertEquiv ν (representation ν (f.permCongr (e.symm.permCongr p))
      ((spaceHilbertEquiv ν).symm (T.toLinearEquiv (spaceHilbertEquiv μ v)))) at hT
  have he : e.permCongr (e.symm.permCongr p)=p := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]
  have hf : f.permCongr (e.symm.permCongr p)=(e.symm.trans f).permCongr p := by
    apply Equiv.ext
    intro x
    rfl
  rw [he,hf,LinearEquiv.symm_apply_apply] at hT
  have ht := congrArg (spaceHilbertEquiv ν).symm hT
  simpa only [LinearEquiv.symm_apply_apply,S,LinearEquiv.trans_apply] using ht

lemma cardRepresentation_distinct (d : ℕ) (μ ν : Shapes (2^d)) (hne : μ≠ν) :
    ¬Nonempty (Representation.Equiv (cardRepresentation d μ) (cardRepresentation d ν)) := by
  rintro ⟨T⟩
  exact hne (Subtype.ext (relabelledUnitary_neq μ.1 ν.1 (cardLabels d μ) (cardLabels d ν) T))

lemma card_conjugacy_shapes (d : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Card d)))≤Fintype.card (Shapes (2^d)) := by
  have h := Nat.card_le_card_of_injective _ (conjugacyPartition_injective (α := Card d))
  simpa only [card_positions,Nat.card_eq_fintype_card,Fintype.card_congr (shapePartitionEquiv (2^d))] using h

lemma row_zero_of_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card) (x : Cell μ) : row x=0 := by
  have hr : μ.row 0=μ.cells := Finset.eq_of_subset_of_card_le
    (Finset.filter_subset _ _) (by rw [←μ.rowLen_eq_card]; exact hμ.ge)
  have hx : x.1∈μ.row 0 := by rw [hr]; exact x.2
  exact (YoungDiagram.mem_row_iff.mp hx).2

lemma tabloid_subsingleton_of_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card) :
    Subsingleton (Tabloid μ) := by
  refine ⟨fun f g => ?_⟩
  apply Subtype.ext
  funext x
  obtain ⟨p,hp⟩ := f.2
  obtain ⟨q,hq⟩ := g.2
  simp only [hp,hq,Function.comp_apply]
  apply Fin.ext
  exact (row_zero_of_full_row μ hμ (p x)).trans (row_zero_of_full_row μ hμ (q x)).symm

lemma representation_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card)
    (p : Equiv.Perm (Cell μ)) : representation μ p=1 := by
  let := tabloid_subsingleton_of_full_row μ hμ
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext f
  change v.1 (tabloidAct p⁻¹ f)=v.1 f
  rw [show tabloidAct p⁻¹ f=f from Subsingleton.elim _ _]

lemma relabelled_full_row {α : Type*} (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card)
    (e : α ≃ Cell μ) (p : Equiv.Perm α) : relabelledUnitary μ e p=1 := by
  change ((spaceHilbertEquiv μ).conjAlgEquiv ℂ) (representation μ (e.permCongr p))=1
  rw [representation_full_row μ hμ,map_one]

end Thorp.Specht
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
variable {G Ω V : Type*} [Group G] [Fintype G] [Fintype Ω] [Nonempty Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
lemma sampleOperator_trivial (ρ : Representation ℂ G V) (hρ : ∀ g,ρ g=1) (P : Ω → G) :
    sampleOperator ρ P=1 := by
  convert sampleOperator_one (Ω := Ω) ρ using 1
  unfold sampleOperator
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  apply ContinuousLinearMap.ext
  intro v
  change ρ (P ω) v=ρ 1 v
  rw [hρ,hρ]

lemma uniformOperator_trivial (ρ : Representation ℂ G V) (hρ : ∀ g,ρ g=1) :
    uniformOperator ρ=1 := by
  rw [←sampleOperator_uniform]
  exact sampleOperator_trivial ρ hρ id

lemma weighted_sub (ρ : Representation ℂ G V) (p q : G → ℝ) :
    weightedOperator ρ (fun g => p g-q g)=weightedOperator ρ p-weightedOperator ρ q := by
  simp only [weightedOperator,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma physical_palindrome_norm (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    ‖sampleOperator ρ (run d d)‖^2=‖sampleOperator ρ (palindromePerm d)‖ := by
  rw [physical_sweep_adjoint d ρ hρ,sampleOperator_palindrome d ρ hρ]
  have h := ContinuousLinearMap.norm_adjoint_comp_self
    ((sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint)
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  simpa only [ContinuousLinearMap.mul_def,←sq] using h.symm

lemma physical_power_bound (d C : ℕ) (hC : 0 < C) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    ‖sampleOperator ρ (run d (C*d))‖^2≤‖sampleOperator ρ (palindromePerm d)‖^C := by
  have he : sampleOperator ρ (run d (C*d))=(sampleOperator ρ (run d d))^C := by
    simp only [sampleOperator_run,←pow_mul,Nat.mul_comm C d]
  rw [he,←physical_palindrome_norm d ρ hρ]
  calc
    _ ≤ (‖sampleOperator ρ (run d d)‖^C)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_pow_le' _ hC) _
    _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm C 2]

end Thorp
namespace Thorp.Specht
open scoped BigOperators Classical

section
open UnitaryFinite

lemma card_fourier_full_row (d t : ℕ) (μ : Shapes (2^d)) (hj : μ.1.card-μ.1.rowLen 0=0) :
    sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t)-uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)=0 := by
  have hr : μ.1.rowLen 0=μ.1.card := by have := rowLen_zero_le_card μ.1; omega
  have ht (p : Equiv.Perm (Card d)) : cardRepresentation d μ p=1 :=
    relabelled_full_row μ.1 hr (cardLabels d μ) p
  rw [sampleOperator_trivial _ ht,uniformOperator_trivial _ ht,sub_self]

end

lemma half_geom_sum (n : ℕ) : (∑ j∈Finset.range n,(1/2:ℝ)^j)≤2 := by
  have he : (∑ j∈Finset.range n,(1/2:ℝ)^j)=2*(1-(1/2:ℝ)^n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [he]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]

lemma shape_weight_sum (N : ℕ) :
    (∑ μ : Shapes N,(1/4:ℝ)^(μ.1.card-μ.1.rowLen 0))≤2 := by
  have he := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Shapes N))) (t := Finset.range (N+1))
    (g := fun μ : Shapes N => μ.1.card-μ.1.rowLen 0)
    (by intro μ _; simp only [Finset.mem_range]; have := μ.2; omega)
    (fun j => (1/4:ℝ)^j)
  rw [←he]
  apply le_trans _ (half_geom_sum (N+1))
  apply Finset.sum_le_sum
  intro j _
  have hc : ((Finset.univ.filter (fun μ : Shapes N => μ.1.card-μ.1.rowLen 0=j)).card:ℝ)≤(2:ℝ)^j := by
    have hh := tail_shapes_count N j
    rw [Fintype.card_subtype] at hh
    exact_mod_cast hh
  simp only [Finset.sum_const,nsmul_eq_mul]
  calc
    _ ≤ (2:ℝ)^j*(1/4:ℝ)^j := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (1/2:ℝ)^j := by rw [←mul_pow]; norm_num

end Thorp.Specht

namespace Thorp
open scoped BigOperators Classical

section
open UnitaryFinite Specht DimensionEstimates Filter

lemma sampleLaw_run (d t : ℕ) : sampleLaw (run d t)=law d t := by
  classical
  funext g
  unfold sampleLaw finiteMean law
  rw [Fintype.card_subtype]
  apply congrArg (fun z : ℝ => z/(Fintype.card (Fin t → Coins d):ℝ))
  convert Finset.sum_boole (R := ℝ) (fun x => run d t x = g) Finset.univ using 1
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with h <;> simp only [h, ite_true, ite_false]

end
open Filter DimensionEstimates

end Thorp

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter UnitaryFinite

lemma fromDistance_eq (d t : ℕ) (σ : Equiv.Perm (Card d)) : fromDistance d t σ=distance d t := by
  unfold fromDistance distance
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ (fun _ => rfl)

end Thorp.Casimir

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.TraceDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

lemma absoluteTrace_even {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) (u : ℕ) :
    absoluteTrace A (2 * (u : ℝ)) =
      (LinearMap.trace ℂ V ((star A * A)^u).toLinearMap).re := by
  have he : (2 : ℝ) * u = ((2*u : ℕ) : ℝ) := by simp
  unfold absoluteTrace
  rw [he, CFC.rpow_eq_pow, CFC.rpow_natCast _ _ (CFC.sqrt_nonneg _),
    pow_mul, pow_two, CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg A)]

lemma Q_square (d : ℕ) (μ : Shapes (2^d)) :
    star (Q d μ) * Q d μ = K d μ.1 (cardLabels d μ) := by
  unfold Q
  rw [physical_sweep_adjoint _ _ (cardRepresentation_unitary d μ)]
  change _ = sampleOperator (cardRepresentation d μ) (palindromePerm d)
  rw [sampleOperator_palindrome _ _ (cardRepresentation_unitary d μ)]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

lemma levelScale_log (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Real.log n ≤ levelScale n k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : 1 ≤ (n : ℝ) / k := (le_div_iff₀ hkp).mpr (by simpa using (show (k : ℝ) ≤ n by exact_mod_cast hkn))
  have hp := mul_le_mul_of_nonneg_right hkR (Real.log_nonneg hratio)
  have hl := Real.log_le_sub_one_of_pos hkp
  have he : Real.log ((n : ℝ) / k) = Real.log n - Real.log k :=
    Real.log_div hn.ne' hkp.ne'
  dsimp [levelScale]
  rw [he] at hp ⊢
  nlinarith

lemma level_shape_term (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Real.exp (-14 * levelScale n k) ≤ ((n : ℝ)^12)⁻¹ * (1/4 : ℝ)^k := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl := levelScale_log n k hk hkn
  have hj := levelScale_ge n k hkn
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at ht
      exact ht
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith
  calc
    _ ≤ Real.exp (-(12 * Real.log n + (k : ℝ) * Real.log 4)) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    _ = _ := by
      rw [neg_add, Real.exp_add]
      congr 1
      · have he : Real.log ((n : ℝ)^12) = 12 * Real.log n := by
          norm_num [Real.log_pow]
        rw [Real.exp_neg, ←he, Real.exp_log (pow_pos hn _)]
      · rw [show -((k : ℝ) * Real.log 4) = (k : ℝ) * (-Real.log 4) by ring,
          Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        norm_num

lemma uniform_nonconstant_decay :
    ∃ u : ℕ, 1 ≤ u ∧ ∀ v : ℕ, u ≤ v →
      ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ),
        0 < μ.card - μ.rowLen 0 →
        (Module.finrank ℂ (hilbertSpace μ) : ℝ)^2 * ‖K d μ e‖^v ≤
          Real.exp (-14 * levelScale (2^d) (μ.card - μ.rowLen 0)) := by
  obtain ⟨a, ha, hlevel⟩ := level_contraction
  obtain ⟨b, hb, hdim⟩ := HarmonicBounds.dimension_contraction
  obtain ⟨m, hm⟩ := exists_nat_ge (max (14/a) (2/b))
  have hma : 14 ≤ a * m := by
    have ht := (div_le_iff₀ ha).mp ((le_max_left _ _).trans hm)
    linarith
  have hmb : 2 ≤ b * m := by
    have ht := (div_le_iff₀ hb).mp ((le_max_right _ _).trans hm)
    linarith
  have hmp : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hma
    norm_num at hma
  refine ⟨2*m, by omega, ?_⟩
  intro v hv d μ e hk
  let D : ℝ := Module.finrank ℂ (space μ)
  let L : ℝ := levelScale (2^d) (μ.card - μ.rowLen 0)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast dimension_pos μ
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by
    dsimp [D]; exact_mod_cast dimension_pos μ)
  have hμ : μ.card = 2^d := by
    rw [←card_cell, ←Fintype.card_congr e, card_positions]
  have hkn : μ.card - μ.rowLen 0 ≤ 2^d := by omega
  have hL : 0 ≤ L := (Nat.cast_nonneg _).trans (levelScale_ge _ _ hkn)
  have h₁ := pow_le_pow_left₀ (norm_nonneg (K d μ e)) (hlevel d μ e hk) m
  have h₂ := pow_le_pow_left₀ (norm_nonneg (K d μ e)) (hdim d μ e hk) m
  change ‖K d μ e‖^m ≤ (Real.exp (-a*L))^m at h₁
  change ‖K d μ e‖^m ≤ (Real.exp (-b*Real.log D))^m at h₂
  have hp : ‖K d μ e‖^v ≤ (Real.exp (-a*L))^m * (Real.exp (-b*Real.log D))^m := by
    apply (pow_le_pow_of_le_one (norm_nonneg _) (K_norm_le_one d μ e) hv).trans
    rw [two_mul, pow_add]
    exact mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _) (by positivity)
  rw [finrank_hilbertSpace]
  change D^2 * ‖K d μ e‖^v ≤ Real.exp (-14*L)
  calc
    _ ≤ D^2 * ((Real.exp (-a*L))^m * (Real.exp (-b*Real.log D))^m) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = Real.exp ((2-b*m)*Real.log D - (a*m)*L) := by
      rw [← Real.exp_log hD, ←Real.exp_nat_mul, ←Real.exp_nat_mul,
        ←Real.exp_nat_mul, ←Real.exp_add, ←Real.exp_add, Real.log_exp]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hfirst : (2-b*m)*Real.log D ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hlogD
      have hlast := mul_le_mul_of_nonneg_right hma hL
      linarith

lemma two_inverse_twelfth_le (x : ℝ) (hx : 2 ≤ x) :
    (x^12)⁻¹ * 2 ≤ x^(-10 : ℤ) := by
  have hxp : 0 < x := by linarith
  have hsq : 2 ≤ x^2 := by nlinarith
  rw [zpow_neg, zpow_ofNat]
  change (x^12)⁻¹ * 2 ≤ (x^10)⁻¹
  have hpow : x^12 = x^10 * x^2 := by ring
  rw [inv_mul_eq_div, inv_eq_one_div]
  apply (div_le_div_iff₀ (pow_pos hxp _) (pow_pos hxp _)).mpr
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_left hsq (pow_nonneg hxp.le 10)]

lemma uniform_tail_bound :
    ∃ u : ℕ, 1 ≤ u ∧ ∀ d : ℕ, 1 ≤ d → ∀ v : ℕ, u ≤ v →
      tailBound d v ≤ ((2 : ℝ)^d)^(-10 : ℤ) := by
  obtain ⟨u, hu, hdec⟩ := uniform_nonconstant_decay
  refine ⟨u, hu, ?_⟩
  intro d hd v hv
  have hn : (2 : ℝ) ≤ (2 : ℝ)^d := by
    calc
      (2 : ℝ) = 2^1 := by norm_num
      _ ≤ 2^d := pow_le_pow_right₀ (by norm_num) hd
  have hterm (μ : Shapes (2^d)) :
      (if μ.1.card - μ.1.rowLen 0 = 0 then 0 else
        (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 * ‖K d μ.1 (cardLabels d μ)‖^v) ≤
      (((2 : ℝ)^d)^12)⁻¹ * (1/4 : ℝ)^(μ.1.card - μ.1.rowLen 0) := by
    split_ifs with hz
    · positivity
    · have hk : 0 < μ.1.card - μ.1.rowLen 0 := by omega
      have hkn : μ.1.card - μ.1.rowLen 0 ≤ 2^d := by have := μ.2; omega
      apply (hdec v hv d μ.1 (cardLabels d μ) hk).trans
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        level_shape_term (2^d) (μ.1.card - μ.1.rowLen 0) hk hkn
  calc
    tailBound d v ≤ ∑ μ : Shapes (2^d),
        (((2 : ℝ)^d)^12)⁻¹ * (1/4 : ℝ)^(μ.1.card - μ.1.rowLen 0) :=
      Finset.sum_le_sum (fun μ _ => hterm μ)
    _ = (((2 : ℝ)^d)^12)⁻¹ * ∑ μ : Shapes (2^d), (1/4 : ℝ)^(μ.1.card - μ.1.rowLen 0) :=
      (Finset.mul_sum ..).symm
    _ ≤ (((2 : ℝ)^d)^12)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left (shape_weight_sum _) (by positivity)
    _ ≤ _ := two_inverse_twelfth_le _ hn

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.TraceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

lemma trace_re_le_dimension_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : V →L[ℂ] V) :
    (LinearMap.trace ℂ V A.toLinearMap).re ≤ (Module.finrank ℂ V : ℝ) * ‖A‖ := by
  let B := stdOrthonormalBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ B.toBasis]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  calc
    _ ≤ ∑ j : Fin (Module.finrank ℂ V), ‖A‖ := by
      apply Finset.sum_le_sum
      intro j _
      change (inner ℂ (B j) (A (B j))).re ≤ ‖A‖
      apply (Complex.re_le_norm _).trans
      apply (norm_inner_le_norm _ _).trans
      simpa only [B.norm_eq_one, one_mul, mul_one] using A.le_opNorm (B j)
    _ = _ := by simp

lemma trace_power_le_dimension_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) (u : ℕ) (hu : 0 < u) :
    (LinearMap.trace ℂ V (A^u).toLinearMap).re ≤
      (Module.finrank ℂ V : ℝ) * ‖A‖^u :=
  (trace_re_le_dimension_norm (A^u)).trans
    (mul_le_mul_of_nonneg_left (norm_pow_le' A hu) (Nat.cast_nonneg _))

lemma full_row_dimension (μ : YoungDiagram) (hμ : μ.rowLen 0 = μ.card) :
    Module.finrank ℂ (hilbertSpace μ) = 1 := by
  rw [finrank_hilbertSpace]
  have hle := Submodule.finrank_le (space μ)
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have hc : Fintype.card (Tabloid μ) ≤ 1 := by
    let := tabloid_subsingleton_of_full_row μ hμ
    exact Fintype.card_le_one_iff.mpr (fun _ _ => Subsingleton.elim _ _)
  exact Nat.le_antisymm (hle.trans hc) (dimension_pos μ)

lemma full_row_unique (n : ℕ) (μ ν : Shapes n)
    (hμ : μ.1.card - μ.1.rowLen 0 = 0) (hν : ν.1.card - ν.1.rowLen 0 = 0) : μ = ν := by
  have hcells (γ : Shapes n) (hγ : γ.1.card - γ.1.rowLen 0 = 0) :
      γ.1.cells = {0} ×ˢ Finset.range n := by
    have hrow : γ.1.rowLen 0 = γ.1.card := by have := rowLen_zero_le_card γ.1; omega
    have he : γ.1.row 0 = γ.1.cells := Finset.eq_of_subset_of_card_le
      (Finset.filter_subset _ _) (by rw [←γ.1.rowLen_eq_card]; exact hrow.ge)
    rw [←he, YoungDiagram.row_eq_prod, hrow, γ.2]
  apply Subtype.ext
  apply YoungDiagram.ext
  exact (hcells μ hμ).trans (hcells ν hν).symm

lemma full_row_count (n : ℕ) :
    (∑ μ : Shapes n, if μ.1.card - μ.1.rowLen 0 = 0 then (1 : ℝ) else 0) ≤ 1 := by
  have hc : (Finset.univ.filter (fun μ : Shapes n => μ.1.card - μ.1.rowLen 0 = 0)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro μ hμ ν hν
    exact full_row_unique n μ ν (Finset.mem_filter.mp hμ).2 (Finset.mem_filter.mp hν).2
  rw [Finset.sum_boole]
  exact_mod_cast hc

lemma full_row_trace (d u : ℕ) (μ : Shapes (2^d)) (hμ : μ.1.card - μ.1.rowLen 0 = 0) :
    (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
      absoluteTrace (V := hilbertSpace μ.1) (Q d μ) (2 * (u : ℝ)) = 1 := by
  have hrow : μ.1.rowLen 0 = μ.1.card := by have := rowLen_zero_le_card μ.1; omega
  have hK : K d μ.1 (cardLabels d μ) = 1 :=
    sampleOperator_trivial (V := hilbertSpace μ.1) _
      (relabelled_full_row μ.1 hrow (cardLabels d μ)) _
  rw [absoluteTrace_even, Q_square, hK, one_pow, full_row_dimension μ.1 hrow]
  simp [full_row_dimension μ.1 hrow]

lemma regularTrace_le (d u : ℕ) (hu : 0 < u) :
    regularTrace d (2 * (u : ℝ)) ≤ 1 + tailBound d u := by
  have hterm (μ : Shapes (2^d)) :
      (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
        absoluteTrace (V := hilbertSpace μ.1) (Q d μ) (2 * (u : ℝ)) ≤
      (if μ.1.card - μ.1.rowLen 0 = 0 then 1 else 0) +
        (if μ.1.card - μ.1.rowLen 0 = 0 then 0 else
          (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 * ‖K d μ.1 (cardLabels d μ)‖^u) := by
    by_cases hz : μ.1.card - μ.1.rowLen 0 = 0
    · simp only [hz, ite_true, add_zero, full_row_trace d u μ hz, le_refl]
    · simp only [hz, ite_false, zero_add]
      rw [absoluteTrace_even, Q_square, pow_two, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (trace_power_le_dimension_norm (V := hilbertSpace μ.1) (K d μ.1 (cardLabels d μ)) u hu) (Nat.cast_nonneg _)
  calc
    regularTrace d (2 * (u : ℝ)) ≤
        (∑ μ : Shapes (2^d), if μ.1.card - μ.1.rowLen 0 = 0 then (1 : ℝ) else 0) +
          tailBound d u := by
      rw [tailBound, ←Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun μ _ => hterm μ)
    _ ≤ _ := add_le_add (full_row_count _) le_rfl

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQW_ThorpRouting.RegularTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

lemma sharp_physical_fourier (d t : ℕ) :
    (2 * distance d t)^2 ≤ ∑ μ : Shapes (2^d),
      (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 *
        ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t) -
          uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)‖^2 := by
  let V : Shapes (2^d) → Type := fun μ => hilbertSpace μ.1
  let : ∀ μ, NormedAddCommGroup (V μ) := fun _ => inferInstance
  let : ∀ μ, InnerProductSpace ℂ (V μ) := fun _ => inferInstance
  let : ∀ μ, FiniteDimensional ℂ (V μ) := fun _ => inferInstance
  let p := fun g : Equiv.Perm (Card d) => law d t g - 1/(Nat.factorial (2^d) : ℝ)
  have hb := FiniteFourier.l1_fourier_bound V (cardRepresentation d)
    (cardRepresentation_unitary d) (cardRepresentation_distinct d) (card_conjugacy_shapes d) p
  have he (μ : Shapes (2^d)) : weightedOperator (V := V μ) (cardRepresentation d μ) p =
      sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t) -
        uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) := by
    rw [sampleOperator_weighted, sampleLaw_run]
    dsimp only [p]
    rw [weighted_sub]
    congr 1
    unfold uniformOperator
    rw [card_permutations]
    simp only [one_div]
  simp_rw [he] at hb
  convert hb using 1
  change (2 * ((1/2 : ℝ) * ∑ g, |p g|))^2 = (∑ g, |p g|)^2
  ring

lemma forward_bound (d v : ℕ) (hv : 0 < v) :
    (2 * distance d (v*d))^2 ≤ tailBound d v := by
  apply (sharp_physical_fourier d (v*d)).trans
  apply Finset.sum_le_sum
  intro μ _
  by_cases hz : μ.1.card - μ.1.rowLen 0 = 0
  · simp [hz, card_fourier_full_row d (v*d) μ hz]
  · simp only [hz, ite_false]
    have hu : uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) = 0 :=
      nontrivial_uniform_zero d μ.1 (cardLabels d μ) (by omega)
    rw [hu, sub_zero]
    exact mul_le_mul_of_nonneg_left
      (physical_power_bound d v hv (cardRepresentation d μ) (cardRepresentation_unitary d μ))
      (sq_nonneg _)

lemma distance_of_tail_bound (d v : ℕ) (hv : 0 < v)
    (ht : tailBound d v ≤ ((2 : ℝ)^d)^(-10 : ℤ)) :
    distance d (v*d) ≤ (1/2 : ℝ) * ((2 : ℝ)^d)^(-5 : ℤ) := by
  have hb := (forward_bound d v hv).trans ht
  have hn : 0 < (2 : ℝ)^d := by positivity
  have he : (((2 : ℝ)^d)^(-5 : ℤ))^2 = ((2 : ℝ)^d)^(-10 : ℤ) := by
    rw [pow_two, ←zpow_add₀ hn.ne']
    norm_num
  have hp : 0 < ((2 : ℝ)^d)^(-5 : ℤ) := zpow_pos hn _
  rw [←he] at hb
  have hh : 2 * distance d (v*d) ≤ ((2 : ℝ)^d)^(-5 : ℤ) := by
    nlinarith [distance_nonneg d (v*d)]
  linarith

theorem regular_trace_smoothing_oai : MainStatement := by
  obtain ⟨u, hu, htail⟩ := uniform_tail_bound
  refine ⟨2 * (u : ℝ), ?_, ?_⟩
  · have h : (1 : ℝ) ≤ u := by exact_mod_cast hu
    linarith
  · intro d hd
    refine ⟨?_, ?_⟩
    · exact (regularTrace_le d u (by omega)).trans
        (add_le_add le_rfl (htail d hd u le_rfl))
    · intro v hv σ
      have hvR : (u : ℝ) ≤ v := by linarith
      have hvZ : (u : ℤ) ≤ v := by exact_mod_cast hvR
      have hv0 : 0 ≤ v := (Int.natCast_nonneg u).trans hvZ
      have hvn : u ≤ v.toNat := by
        rw [←Int.toNat_of_nonneg hv0] at hvZ
        exact_mod_cast hvZ
      change fromDistance d (v.toNat*d) σ ≤ _
      rw [fromDistance_eq]
      exact distance_of_tail_bound d v.toNat (by omega) (htail d hd v.toNat hvn)

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
end

theorem solution : type_of% @OAI.ThorpNine.Harmonic.Thorp.LowPlanes.regular_trace_smoothing_oai := @OAI.ThorpNine.Harmonic.Thorp.LowPlanes.regular_trace_smoothing_oai
