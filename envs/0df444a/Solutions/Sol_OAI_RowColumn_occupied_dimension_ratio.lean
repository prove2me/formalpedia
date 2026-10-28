-- Prove2me | solution 1 for OAI.RowColumn.occupied_dimension_ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:04:03.680078+00:00
-- url     : https://prove2.me/submissions/37e5e6f7-4e23-4b88-ac1c-c847397af5a6

import Mathlib
import Definitions.Def_OccupiedOverlap
import Definitions.Def_OAIW2RC000
import Theorems.Thm_OAI_RowColumn_MatrixState_occupied_commutant_trace

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Action
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.UnitaryFinite
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

end CubeShuffle.UnitaryFinite

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

lemma alternator_apply_action (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V) :
    alternator C ρ (ρ c v) = permSign (c : Equiv.Perm α) • alternator C ρ v := by
  exact congrArg (fun T : Module.End ℂ V => T v) (alternator_mul C ρ c)

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

lemma space_ne_bot (μ : YoungDiagram) : space μ ≠ ⊥ := by
  intro h
  have he := polytabloid_mem_space μ
  rw [h,Submodule.mem_bot] at he
  exact polytabloid_ne_zero μ he

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

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

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

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Reconstruction
attribute [-instance] _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ComplexOrder
noncomputable section
open scoped ComplexConjugate
namespace RowColumn.FiniteStarAlgebra
variable {A : Type*} [Ring A] [Module ℂ A] [StarRing A] [FiniteDimensional ℂ A]

/-- A finite-dimensional two-sided star ideal has a central orthogonal unit.
The two inner-product identities hold for the actual Hilbert–Schmidt trace.
This constructs the central support used in the occupied-board filter. -/
theorem complementary_central_projection (core : InnerProductSpace.Core ℂ A) (K : Submodule ℂ A)
    (hL : ∀ a x, x ∈ K → a*x ∈ K) (hR : ∀ a x, x ∈ K → x*a ∈ K)
    (hstar : ∀ x, x ∈ K → star x ∈ K)
    (hadjL : ∀ a x y : A, core.inner (a*x) y = core.inner x (star a*y))
    (hadjR : ∀ a x y : A, core.inner (x*a) y = core.inner x (y*star a)) :
    ∃ q : A, star q = q ∧ q*q = q ∧ (∀ a, q*a = a*q) ∧
      1-q ∈ K ∧ (∀ x, x ∈ K → q*x = 0 ∧ x*q = 0) := by
  let : NormedAddCommGroup A := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ A := InnerProductSpace.ofCore { __ := core }
  change ∀ a x y : A, inner ℂ (a*x) y = inner ℂ x (star a*y) at hadjL
  change ∀ a x y : A, inner ℂ (x*a) y = inner ℂ x (y*star a) at hadjR
  have hoL (a x : A) (hx : x ∈ Kᗮ) : a*x ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    have hh := hx (star a*y) (hL (star a) y hy)
    simpa only [hadjL, star_star] using hh
  have hoR (a x : A) (hx : x ∈ Kᗮ) : x*a ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    have hh := hx (y*star a) (hR (star a) y hy)
    simpa only [hadjR, star_star] using hh
  have hz (x : A) (hk : x ∈ K) (ho : x ∈ Kᗮ) : x = 0 :=
    (inner_self_eq_zero (𝕜 := ℂ)).mp ((K.mem_orthogonal x).mp ho x hk)
  let k : A := K.starProjection 1
  let q : A := 1-k
  have hk : k ∈ K := (K.orthogonalProjectionOnto 1).property
  have hq : q ∈ Kᗮ := K.sub_starProjection_mem_orthogonal 1
  have hqa (x : A) (hx : x ∈ K) : q*x = 0 :=
    hz _ (hL q x hx) (hoR x q hq)
  have haq (x : A) (hx : x ∈ K) : x*q = 0 :=
    hz _ (hR q x hx) (hoL x q hq)
  have hsk : star k = k := by
    have e₁ : star k = k*star k := by
      have he := hqa (star k) (hstar k hk)
      change (1-k)*star k = 0 at he
      simpa only [sub_mul, one_mul, sub_eq_zero] using he
    have e₂ := congrArg star e₁
    simp only [star_star, star_mul] at e₂
    exact e₁.trans e₂.symm
  refine ⟨q, ?_, ?_, ?_, ?_, fun x hx => ⟨hqa x hx, haq x hx⟩⟩
  · simp only [q, star_sub, star_one, hsk]
  · change q*(1-k) = q
    rw [mul_sub, mul_one, hqa k hk, sub_zero]
  · intro a
    have hka : k*a = k*a*k := by
      have he := haq (k*a) (hR a k hk)
      change (k*a)*(1-k) = 0 at he
      simpa only [mul_sub, mul_one, sub_eq_zero] using he
    have hak : a*k = k*a*k := by
      have he := hqa (a*k) (hL a k hk)
      change (1-k)*(a*k) = 0 at he
      simpa only [sub_mul, one_mul, sub_eq_zero, ← mul_assoc] using he
    change (1-k)*a = a*(1-k)
    rw [sub_mul, one_mul, mul_sub, mul_one]
    exact congrArg (fun z => a-z) (hka.trans hak.symm)
  · simpa only [q, sub_sub_cancel] using hk

end RowColumn.FiniteStarAlgebra

namespace RowColumn.FiniteStarAlgebra
open scoped ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma core_inner_trace (A : StarSubalgebra ℂ (Ambient (E := E))) (a b : A) :
    (algebraCore A).inner a b = physicalTrace A (star a*b) := by
  change LinearMap.trace ℂ E (LinearMap.adjoint (a : Ambient (E := E)).toLinearMap ∘ₗ
    (b : Ambient (E := E)).toLinearMap) = LinearMap.trace ℂ E ((star (a : Ambient (E := E)) * (b : Ambient (E := E))).toLinearMap)
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_toLinearMap]
  rfl

lemma physicalTrace_mul_comm (A : StarSubalgebra ℂ (Ambient (E := E))) (a b : A) :
    physicalTrace A (a*b) = physicalTrace A (b*a) :=
  LinearMap.trace_comp_comm' (b : Ambient (E := E)).toLinearMap (a : Ambient (E := E)).toLinearMap

/-- Central support of a reducing physical subspace. Its algebraic kernel is
removed, so no other unsupported sector can inflate the Fourier norm. -/
theorem exists_central_support (A : StarSubalgebra ℂ (Ambient (E := E))) (F : Submodule ℂ E)
    (hF : ∀ a : A, ∀ x ∈ F, (a : Ambient (E := E)) x ∈ F) :
    ∃ q : A, star q = q ∧ q*q=q ∧ (∀ a, q*a=a*q) ∧
      restrictHom A F hF q = 1 ∧
      (∀ a : A, restrictHom A F hF a = 0 → q*a=0) := by
  let : FiniteDimensional ℂ A := FiniteDimensional.of_injective
    (algebraToEnd A) (algebraToEnd_injective A)
  let φ := restrictHom A F hF
  let K := LinearMap.ker φ.toLinearMap
  have hk (a : A) : a ∈ K ↔ φ a = 0 := Iff.rfl
  obtain ⟨q,hs,hqq,hc,hkq,hkill⟩ := complementary_central_projection (algebraCore A) K
    (fun a x hx => by rw [hk, map_mul, (hk x).mp hx, mul_zero])
    (fun a x hx => by rw [hk, map_mul, (hk x).mp hx, zero_mul])
    (fun x hx => by rw [hk, map_star, (hk x).mp hx]; exact star_zero (F →L[ℂ] F))
    (fun a x y => by simp only [core_inner_trace, star_mul, mul_assoc])
    (fun a x y => by
      simp only [core_inner_trace, star_mul]
      rw [mul_assoc, physicalTrace_mul_comm A (star a) _, mul_assoc])
  refine ⟨q,hs,hqq,hc,?_,fun a ha => (hkill a ((hk a).mpr ha)).1⟩
  have hh := (hk (1-q)).mp hkq
  have he : 1-φ q=0 := by simpa only [map_sub, map_one] using hh
  exact (sub_eq_zero.mp he).symm

end RowColumn.FiniteStarAlgebra
noncomputable section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.Isotypic
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)

lemma projection_intertwines (F : Submodule ℂ E)
    (hF : ∀ g x, x ∈ F → τ g x ∈ F)
    (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y) :
    ∀ g x, F.starProjection (τ g x) = τ g (F.starProjection x) := by
  intro g x
  let e : E →ₗᵢ[ℂ] E := (τ g).isometryOfInner (hτ g)
  have hmap : F.map e.toLinearMap = F := by
    apply le_antisymm
    · rintro _ ⟨y,hy,rfl⟩
      exact hF g y hy
    · intro y hy
      refine ⟨τ g⁻¹ y, hF g⁻¹ y hy, ?_⟩
      change (τ g * τ g⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
  have he := e.map_starProjection F x
  simpa only [hmap, e, LinearMap.coe_isometryOfInner] using he.symm

omit [FiniteDimensional ℂ V] in
/-- On an isotypic unitary representation, every eigenspace of an operator in
the group commutant has dimension at least that of the irreducible type. -/
theorem eigenspace_finrank [Representation.IsIrreducible ρ]
    (hspan : carrier ρ τ = ⊤)
    (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y)
    (T : E →ₗ[ℂ] E) (hT : ∀ g x, T (τ g x) = τ g (T x))
    (μ : ℂ) (hμ : Module.End.HasEigenvalue T μ) :
    Module.finrank ℂ V ≤ Module.finrank ℂ (Module.End.eigenspace T μ) := by
  classical
  let F := Module.End.eigenspace T μ
  have hf (g : G) (x : E) (hx : x ∈ F) : τ g x ∈ F := by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hT, hx, map_smul]
  let P : Representation.IntertwiningMap τ τ :=
    { toLinearMap := F.starProjection.toLinearMap
      isIntertwining' g := by ext x; exact projection_intertwines τ F hf hτ g x }
  have hex : ∃ f : Representation.IntertwiningMap ρ τ, P.comp f ≠ 0 := by
    by_contra! h
    have hz (x : E) (hx : x ∈ carrier ρ τ) : P x = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨f,v⟩,rfl⟩ := hx
        exact congrArg (fun L : Representation.IntertwiningMap ρ τ => L v) (h f)
      | zero => exact map_zero P
      | add x y hx hy hpx hpy => simp only [map_add, hpx, hpy, add_zero]
      | smul c x hx hpx => simp only [map_smul, hpx, smul_zero]
    obtain ⟨x,hx,hxn⟩ := hμ.exists_hasEigenvector
    have he := hz x (by rw [hspan]; trivial)
    change F.starProjection x = 0 at he
    rw [F.starProjection_eq_self_iff.mpr hx] at he
    exact hxn he
  obtain ⟨f,hfne⟩ := hex
  have hi : Function.Injective (P.comp f) :=
    (Representation.IsIrreducible.injective_or_eq_zero (P.comp f)).resolve_right hfne
  let L : V →ₗ[ℂ] F := (P.comp f).toLinearMap.codRestrict F (fun v =>
    (F.orthogonalProjectionOnto (f v)).property)
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro x y h
  exact hi (congrArg Subtype.val h)

end RowColumn.Isotypic
namespace RowColumn.Isotypic
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma carrier_commutant (T : E →ₗ[ℂ] E) (hT : ∀ g x, T (τ g x) = τ g (T x))
    (x : E) (hx : x ∈ carrier ρ τ) : T x ∈ carrier ρ τ := by
  let t : Representation.IntertwiningMap τ τ :=
    { toLinearMap := T
      isIntertwining' g := by ext x; exact hT g x }
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨f,v⟩,rfl⟩ := hx
    exact mem_carrier ρ τ (t.comp f) v
  | zero => simpa only [map_zero] using (carrier ρ τ).zero_mem
  | add x y hx hy hx' hy' => simpa only [map_add] using (carrier ρ τ).add_mem hx' hy'
  | smul c x hx hx' => simpa only [map_smul] using (carrier ρ τ).smul_mem c hx'

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma restricted_unitary (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y) :
    ∀ g (x y : carrier ρ τ), inner ℂ (restricted ρ τ g x) (restricted ρ τ g y) = inner ℂ x y := by
  intro g x y
  exact hτ g x y

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma restricted_isotypic : carrier ρ (restricted ρ τ) = ⊤ := by
  let F := carrier ρ τ
  let K := (carrier ρ (restricted ρ τ)).map F.subtype
  have hFK : F ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨f,v⟩,rfl⟩
    exact ⟨restrictIntertwiner ρ τ f v, mem_carrier ρ (restricted ρ τ)
      (restrictIntertwiner ρ τ f) v, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y,hy,hxy⟩ := hFK x.property
  have he : y=x := Subtype.ext hxy
  exact he ▸ hy

end RowColumn.Isotypic
noncomputable section
open scoped BigOperators ComplexOrder
namespace RowColumn.SpectralMultiplicity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma positive_norm_le_of_eigenvalues (T : E →L[ℂ] E) (hT : T.IsPositive)
    (c : ℝ) (hc : 0 ≤ c)
    (hval : ∀ i, hT.toLinearMap.isSymmetric.eigenvalues rfl i ≤ c) : ‖T‖ ≤ c := by
  let b := hT.toLinearMap.isSymmetric.eigenvectorBasis rfl
  apply T.opNorm_le_bound hc
  intro x
  apply le_of_sq_le_sq _ (mul_nonneg hc (norm_nonneg _))
  rw [← b.repr.norm_map (T x), ← b.repr.norm_map x, mul_pow]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := hT.toLinearMap.nonneg_eigenvalues rfl i
  have he := hT.toLinearMap.isSymmetric.eigenvectorBasis_apply_self_apply rfl x i
  change (b.repr (T x)) i = _ at he
  change ‖(b.repr (T x)) i‖^2 ≤ _
  rw [he, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hi, mul_pow]
  exact mul_le_mul_of_nonneg_right (sq_le_sq₀ hi hc |>.mpr (hval i)) (sq_nonneg _)

/-- An eigenvalue supported on at least d dimensions pays a trace factor d.
This is the precise spectral normalization needed for the global filter. -/
theorem norm_le_trace_div (T : E →L[ℂ] E) (hT : T.IsPositive) (d : ℕ) (hd : 0 < d)
    (hmult : ∀ μ : ℂ, Module.End.HasEigenvalue T.toLinearMap μ →
      d ≤ Module.finrank ℂ (Module.End.eigenspace T.toLinearMap μ)) :
    ‖T‖ ≤ (LinearMap.trace ℂ E T.toLinearMap).re / d := by
  have htrace : 0 ≤ (LinearMap.trace ℂ E T.toLinearMap).re :=
    (Complex.nonneg_iff.mp hT.toLinearMap.trace_nonneg).1
  apply positive_norm_le_of_eigenvalues T hT _ (div_nonneg htrace (by positivity))
  intro i
  let μ := hT.toLinearMap.isSymmetric.eigenvalues rfl i
  have hμ : 0 ≤ μ := hT.toLinearMap.nonneg_eigenvalues rfl i
  have hcount := hmult (μ : ℂ) (hT.toLinearMap.isSymmetric.hasEigenvalue_eigenvalues rfl i)
  have hcard := hT.toLinearMap.isSymmetric.card_filter_eigenvalues_eq rfl (μ : ℂ)
  rw [← hcard] at hcount
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inj] at hcount
  apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
  calc
    μ * (d : ℝ) ≤ μ * ((Finset.univ.filter fun j =>
      hT.toLinearMap.isSymmetric.eigenvalues rfl j = μ).card : ℕ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hμ
    _ = ∑ j ∈ Finset.univ.filter (fun j =>
      hT.toLinearMap.isSymmetric.eigenvalues rfl j = μ),
        hT.toLinearMap.isSymmetric.eigenvalues rfl j := by
      symm
      calc
        _ = ∑ j ∈ Finset.univ.filter (fun j =>
          hT.toLinearMap.isSymmetric.eigenvalues rfl j = μ), μ :=
            Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2)
        _ = _ := by simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ j, hT.toLinearMap.isSymmetric.eigenvalues rfl j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hT.toLinearMap.nonneg_eigenvalues rfl j)
    _ = _ := (hT.toLinearMap.isSymmetric.re_trace_eq_sum_eigenvalues rfl).symm

end RowColumn.SpectralMultiplicity
noncomputable section
open scoped ComplexOrder
namespace RowColumn.SpectralMultiplicity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma trace_compression (T : E →L[ℂ] E) (F : Submodule ℂ E) :
    LinearMap.trace ℂ F (F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL).toLinearMap =
      LinearMap.trace ℂ E (T ∘L F.starProjection).toLinearMap := by
  have he := LinearMap.trace_comp_comm' (T.toLinearMap ∘ₗ F.subtype)
    F.orthogonalProjectionOnto.toLinearMap
  exact he

lemma trace_compression_le (T : E →L[ℂ] E) (hT : T.IsPositive)
    (F : Submodule ℂ E) :
    (LinearMap.trace ℂ F (F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL).toLinearMap).re ≤
      (LinearMap.trace ℂ E T.toLinearMap).re := by
  have hp := (hT.orthogonalProjectionOnto_comp Fᗮ).toLinearMap.trace_nonneg
  have hn := (Complex.nonneg_iff.mp hp).1
  rw [trace_compression] at hn ⊢
  have he : F.starProjection + Fᗮ.starProjection = (1 : E →L[ℂ] E) := by
    ext x
    exact F.starProjection_add_starProjection_orthogonal x
  have ht : T ∘L F.starProjection + T ∘L Fᗮ.starProjection = T := by
    rw [← ContinuousLinearMap.comp_add, he]
    rfl
  have htr := congrArg (fun S : E →L[ℂ] E => (LinearMap.trace ℂ E S.toLinearMap).re) ht
  simp only [ContinuousLinearMap.toLinearMap_add, map_add, Complex.add_re] at htr
  linarith

lemma restrict_positive (T : E →L[ℂ] E) (hT : T.IsPositive)
    (F : Submodule ℂ E) (hF : ∀ x ∈ F, T x ∈ F) : (T.restrict hF).IsPositive := by
  have he : T.restrict hF = F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL := by
    ext x
    change T x = F.starProjection (T x)
    exact (F.starProjection_eq_self_iff.mpr (hF x x.property)).symm
  rw [he]
  exact hT.orthogonalProjectionOnto_comp F

lemma trace_restrict_le (T : E →L[ℂ] E) (hT : T.IsPositive)
    (F : Submodule ℂ E) (hF : ∀ x ∈ F, T x ∈ F) :
    (LinearMap.trace ℂ F (T.restrict hF).toLinearMap).re ≤
      (LinearMap.trace ℂ E T.toLinearMap).re := by
  have he : T.restrict hF = F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL := by
    ext x
    change T x = F.starProjection (T x)
    exact (F.starProjection_eq_self_iff.mpr (hF x x.property)).symm
  rw [he]
  exact trace_compression_le T hT F

end RowColumn.SpectralMultiplicity

end
end
end
end
end
end
end


section
noncomputable section
open scoped ComplexOrder
namespace RowColumn.FiniteStarAlgebra
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma supported_restriction_norm (A : StarSubalgebra ℂ (E →L[ℂ] E)) (F : Submodule ℂ E)
    (φ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (q : A) (hs : star q=q) (hqq : q*q=q) (hc : ∀ a, q*a=a*q)
    (hq : φ q=1) (hkill : ∀ a : A, φ a=0 → q*a=0) (a : A) :
    ‖q*a‖ = ‖φ a‖ := by
  let J : NonUnitalStarSubalgebra ℂ A :=
    { carrier := {x | q*x=x}
      zero_mem' := mul_zero q
      add_mem' := by intro x y hx hy; change q*(x+y)=x+y; rw [mul_add,hx,hy]
      mul_mem' := by intro x y hx hy; change q*(x*y)=x*y; rw [← mul_assoc,hx]
      smul_mem' := by intro c x hx; change q*(c • x)=c • x; rw [mul_smul_comm,hx]
      star_mem' := by
        intro x hx
        change q*star x=star x
        rw [hc]
        simpa only [star_mul,hs] using congrArg star hx }
  let : IsClosed (J : Set A) := isClosed_eq (continuous_const.mul continuous_id) continuous_id
  let ψ : J →⋆ₙₐ[ℂ] (F →L[ℂ] F) := φ.toNonUnitalStarAlgHom.comp (NonUnitalStarSubalgebraClass.subtype J)
  have hinj : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    have he : φ ((x : A)-(y : A))=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have hz := hkill _ he
    change q*((x : A)-(y : A))=0 at hz
    rw [mul_sub,x.property,y.property] at hz
    exact sub_eq_zero.mp hz
  let x : J := ⟨q*a,by change q*(q*a)=q*a; rw [← mul_assoc,hqq]⟩
  have hh := NonUnitalStarAlgHom.norm_map ψ hinj x
  change ‖φ (q*a)‖ = ‖q*a‖ at hh
  rw [map_mul,hq,one_mul] at hh
  exact hh.symm

/-- The exact dimension normalization of the occupied-board global filter.
No highest-weight entropy or Schur--Weyl hypothesis is required: restriction
of the supported algebra is faithful, and every eigenspace contains the
irreducible carrier. -/
theorem exists_isotypic_filter (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (τ : Representation ℂ G E)
    (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y)
    (A : StarSubalgebra ℂ (E →L[ℂ] E))
    (hA : ∀ a : A, ∀ g x, (a : E →L[ℂ] E) (τ g x) = τ g ((a : E →L[ℂ] E) x)) :
    ∃ q : A, star q = q ∧ q*q=q ∧ (∀ a, q*a=a*q) ∧
      (∀ x ∈ Isotypic.carrier ρ τ, (q : E →L[ℂ] E) x = x) ∧
      ∀ a : A, (a : E →L[ℂ] E).IsPositive →
        ‖q*a‖ ≤ (physicalTrace A a).re / Module.finrank ℂ V := by
  let : Nontrivial V := by
    let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    exact ρ.asModuleEquiv.symm.toEquiv.nontrivial
  let F := Isotypic.carrier ρ τ
  have hF : ∀ a : A, ∀ x ∈ F, (a : E →L[ℂ] E) x ∈ F := fun a =>
    Isotypic.carrier_commutant ρ τ (a : E →L[ℂ] E).toLinearMap (hA a)
  let φ := restrictHom A F hF
  obtain ⟨q,hqs,hqq,hqc,hq,hkill⟩ := exists_central_support A F hF
  refine ⟨q,hqs,hqq,hqc,?_,?_⟩
  · intro x hx
    exact congrArg Subtype.val (congrArg (fun T : F →L[ℂ] F => T ⟨x,hx⟩) hq)
  · intro a ha
    rw [supported_restriction_norm A F φ q hqs hqq hqc hq hkill a]
    have hp : (φ a).IsPositive := SpectralMultiplicity.restrict_positive
      (a : E →L[ℂ] E) ha F (hF a)
    apply (SpectralMultiplicity.norm_le_trace_div (φ a) hp (Module.finrank ℂ V)
      (Module.finrank_pos) ?_).trans
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact SpectralMultiplicity.trace_restrict_le (a : E →L[ℂ] E) ha F (hF a)
    · intro μ hμ
      apply Isotypic.eigenspace_finrank ρ (Isotypic.restricted ρ τ)
        (Isotypic.restricted_isotypic ρ τ) (Isotypic.restricted_unitary ρ τ hτ)
        (φ a).toLinearMap _ μ hμ
      intro g x
      apply Subtype.ext
      exact hA a g x

end RowColumn.FiniteStarAlgebra
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_HilbertSchmidt
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

lemma trace_toEuclideanCLM (A : Matrix I I ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ I)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A).toLinearMap = A.trace := by
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun I ℂ).toBasis

end RowColumn.MatrixState

end
end

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
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
variable (odd : C → Prop) [DecidablePred odd]


variable {odd} {k : ℕ}

omit [DecidableEq C] in
lemma representation_unitary : CubeShuffle.UnitaryFinite.IsUnitary
    (representation (S := S) (odd := odd) (k := k)) := by
  intro g v z
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ w, inner ℂ (permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w))
      (permSign (oddPerm g⁻¹ w) * z (actWord g⁻¹ w))) = _
  have hh (w : Words (S := S) odd k) :
      inner ℂ (permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w))
        (permSign (oddPerm g⁻¹ w) * z (actWord g⁻¹ w)) =
      inner ℂ (v (actWord g⁻¹ w)) (z (actWord g⁻¹ w)) := by
    simp only [RCLike.inner_apply, map_mul, conj_permSign]
    rw [show permSign (oddPerm g⁻¹ w) * z (actWord g⁻¹ w) *
        (permSign (oddPerm g⁻¹ w) * (starRingEnd ℂ) (v (actWord g⁻¹ w))) =
      (permSign (oddPerm g⁻¹ w) * permSign (oddPerm g⁻¹ w)) *
        (z (actWord g⁻¹ w) * (starRingEnd ℂ) (v (actWord g⁻¹ w))) by ring,
      permSign_sq, one_mul]
  simp_rw [hh]
  exact Equiv.sum_comp (wordsEquiv g⁻¹) (fun w => inner ℂ (v w) (z w))

end RowColumn.Signed

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

lemma sum_wordVectors (x : EuclideanSpace ℂ (Words (S := S) odd k)) :
    (∑ w, x w • wordVector w) = x := by
  ext z
  simp [WithLp.ofLp_sum, wordVector, WithLp.ofLp_smul]

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
-- module Solutions.OAIW2_RowColumn.RowColumn_CopyOverlap
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace RowColumn
open scoped BigOperators ComplexConjugate Classical

section HilbertSchmidt
variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

lemma hilbertSchmidtSq_eq_sum (B : V →L[ℂ] W)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ V) :
    hilbertSchmidtSq B = ∑ i, ‖B (b i)‖ ^ 2 := by
  rw [hilbertSchmidtSq, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa using (B.apply_norm_sq_eq_inner_adjoint_right (b i)).symm

lemma norm_sq_le_hilbertSchmidtSq (B : V →L[ℂ] W) :
    ‖B‖ ^ 2 ≤ hilbertSchmidtSq B := by
  let b := stdOrthonormalBasis ℂ V
  have hn : 0 ≤ hilbertSchmidtSq B := by
    rw [hilbertSchmidtSq_eq_sum B b]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh : ‖B‖ ≤ Real.sqrt (hilbertSchmidtSq B) := by
    apply B.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    have ha : ‖B x‖ ≤ ∑ i, ‖inner ℂ (b i) x‖ * ‖B (b i)‖ := by
      nth_rw 1 [← b.sum_repr' x]
      rw [map_sum]
      apply (norm_sum_le _ _).trans
      simp only [map_smul, norm_smul]
      exact le_rfl
    have hb := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => ‖inner ℂ (b i) x‖) (fun i => ‖B (b i)‖)
    rw [b.sum_sq_norm_inner_right, Real.sqrt_sq (norm_nonneg x),
      ← hilbertSchmidtSq_eq_sum B b, mul_comm] at hb
    exact ha.trans hb
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (Real.sq_sqrt hn)

end HilbertSchmidt

section CopyTrace
variable {V W X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  {u v : ℕ}

lemma hilbertSchmidtSq_overlap (I : V →ₗᵢ[ℂ] X) (J : W →ₗᵢ[ℂ] X) :
    hilbertSchmidtSq (I.toContinuousLinearMap.adjoint.comp J.toContinuousLinearMap) =
      (LinearMap.trace ℂ X
        ((I.toContinuousLinearMap.comp I.toContinuousLinearMap.adjoint).comp
          (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint)).toLinearMap).re := by
  unfold hilbertSchmidtSq
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.toLinearMap_comp]
  congr 1
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

/-- The all-copy identity in weighted.tex:126–133, for the actual embeddings.
No overlap bound is an assumption. -/
lemma allCopy_hilbertSchmidt_identity (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) :
    ∑ i, ∑ j, hilbertSchmidtSq
      ((I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap) =
    (LinearMap.trace ℂ X ((copyProjection I).comp (copyProjection J)).toLinearMap).re := by
  change _ = (LinearMap.trace ℂ X
    ((∑ i, (I i).toContinuousLinearMap.comp (I i).toContinuousLinearMap.adjoint) *
      (∑ j, (J j).toContinuousLinearMap.comp (J j).toContinuousLinearMap.adjoint)).toLinearMap).re
  simp only [Finset.sum_mul, Finset.mul_sum, ContinuousLinearMap.toLinearMap_sum,
    map_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact hilbertSchmidtSq_overlap (I i) (J j)

lemma allCopyOverlap_le_trace (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) :
    allCopyOverlap I J ≤
      (LinearMap.trace ℂ X ((copyProjection I).comp (copyProjection J)).toLinearMap).re := by
  rw [← allCopy_hilbertSchmidt_identity I J]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact norm_sq_le_hilbertSchmidtSq _

end CopyTrace
end RowColumn

end
end

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

lemma isometry_adjoint_apply (I : V →ₗᵢ[ℂ] X) (x : V) :
    I.toContinuousLinearMap.adjoint (I x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact I.inner_map_map y x

lemma isometry_adjoint_comp (I : V →ₗᵢ[ℂ] X) :
    I.toContinuousLinearMap.adjoint.comp I.toContinuousLinearMap = 1 := by
  ext x
  exact isometry_adjoint_apply I x

lemma copyProjection_positive (I : Fin u → V →ₗᵢ[ℂ] X) :
    (copyProjection I).IsPositive := by
  apply ContinuousLinearMap.isPositive_sum
  intro i _
  exact ContinuousLinearMap.isPositive_self_comp_adjoint _

lemma copyProjection_trace (I : Fin u → V →ₗᵢ[ℂ] X) :
    LinearMap.trace ℂ X (copyProjection I).toLinearMap = (u * Module.finrank ℂ V : ℕ) := by
  simp only [copyProjection, ContinuousLinearMap.toLinearMap_sum, map_sum,
    ContinuousLinearMap.toLinearMap_comp]
  have h (i : Fin u) : LinearMap.trace ℂ X
      ((I i).toContinuousLinearMap.toLinearMap.comp (I i).toContinuousLinearMap.adjoint.toLinearMap) =
      (Module.finrank ℂ V : ℂ) := by
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ V ((I i).toContinuousLinearMap.adjoint.comp
      (I i).toContinuousLinearMap).toLinearMap = _
    rw [isometry_adjoint_comp]
    exact LinearMap.trace_id ℂ V
  simp_rw [h]
  simp [Nat.cast_mul]

lemma copyProjection_intertwines [Group G] (ρ : Representation ℂ G V) (τ : Representation ℂ G X)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ) (I : Fin u → V →ₗᵢ[ℂ] X)
    (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap) :
    Intertwines τ τ (copyProjection I).toLinearMap := by
  intro g x
  simp only [copyProjection, ContinuousLinearMap.coe_coe, sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (I i).toContinuousLinearMap.adjoint (τ g x) =
    ρ g ((I i).toContinuousLinearMap.adjoint x) from
    adjoint_intertwines (I i).toLinearMap (hI i) hρ hτ g x]
  exact hI i g _

lemma allCopyOverlap_comp_isometry (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) (K : X →ₗᵢ[ℂ] E) :
    allCopyOverlap (fun i => K.comp (I i)) (fun j => K.comp (J j)) = allCopyOverlap I J := by
  unfold allCopyOverlap
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun T : W →L[ℂ] V => ‖T‖^2)
  ext x
  change (K.toContinuousLinearMap.comp (I i).toContinuousLinearMap).adjoint
    (K (J j x)) = _
  rw [ContinuousLinearMap.adjoint_comp]
  change (I i).toContinuousLinearMap.adjoint (K.toContinuousLinearMap.adjoint (K (J j x))) = _
  rw [isometry_adjoint_apply]
  rfl

end RowColumn

end
end


section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.UnitaryFinite
variable {G V E : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)
  (hρ : IsUnitary ρ) (hτ : IsUnitary τ)

include hρ hτ

/-- Every actual nonzero algebraic embedding of irreducible unitary carriers
normalizes to an isometric intertwiner. No normalized embedding is assumed. -/
theorem isometric_intertwiner_of_injective [Representation.IsIrreducible ρ]
    (f : Representation.IntertwiningMap ρ τ) (hf : Function.Injective f) :
    ∃ I : V →ₗᵢ[ℂ] E, ∀ g x, I (ρ g x)=τ g (I x) := by
  let : Nontrivial V := by
    let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    exact ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨c,hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective
      (gramIntertwiner ρ τ hρ hτ f)
  have hgram : (LinearMap.adjoint f.toLinearMap).comp f.toLinearMap = c • LinearMap.id := by
    change (gramIntertwiner ρ τ hρ hτ f).toLinearMap = _
    rw [← hc]
    rfl
  have hn (x : V) : ‖f x‖^2 = c.re * ‖x‖^2 := by
    have hh := congrArg (fun T : V →ₗ[ℂ] V => inner ℂ x (T x)) hgram
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.smul_apply,
      LinearMap.id_apply, inner_smul_right, inner_self_eq_norm_sq_to_K] at hh
    change ‖f.toLinearMap x‖^2 = c.re * ‖x‖^2
    have he := congrArg Complex.re hh
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero] using he
  obtain ⟨x,hx⟩ := exists_ne (0 : V)
  have hfx : f x ≠ 0 := by intro h; exact hx (hf (h.trans (map_zero f).symm))
  have hcpos : 0 < c.re := by
    have hh := hn x
    have hp : 0 < ‖f x‖^2 := sq_pos_of_ne_zero ((norm_ne_zero_iff).mpr hfx)
    have hxnon : 0 ≤ ‖x‖^2 := sq_nonneg _
    nlinarith
  let a : ℂ := (Real.sqrt c.re)⁻¹
  let F : V →ₗ[ℂ] E := a • f.toLinearMap
  have ha : ‖a‖^2 * c.re = 1 := by
    simp only [a, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [inv_pow, Real.sq_sqrt hcpos.le, inv_mul_cancel₀ (ne_of_gt hcpos)]
  have hnorm (y : V) : ‖F y‖ = ‖y‖ := by
    change ‖a • f y‖=‖y‖
    rw [norm_smul]
    have hh : (‖a‖*‖f y‖)^2=‖y‖^2 := by rw [mul_pow, hn, ← mul_assoc, ha, one_mul]
    exact (sq_eq_sq₀ (mul_nonneg (norm_nonneg a) (norm_nonneg (f y))) (norm_nonneg y)).mp hh
  let I : V →ₗᵢ[ℂ] E := { F with norm_map' := hnorm }
  refine ⟨I,?_⟩
  intro g y
  change a • f (ρ g y)=τ g (a • f y)
  rw [Representation.IntertwiningMap.isIntertwining, map_smul]
end RowColumn

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Sectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder

noncomputable section
namespace RowColumn.Signed
open scoped Classical
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] in
lemma frame_pred_congr (p q : S → Prop) [dp : DecidablePred p] [dq : DecidablePred q]
    (hp : Fintype.card {x : S // p x} = k)
    (hq : Fintype.card {x : S // q x} = k)
    (he : p = q) (x : S) (hx : p x) (hy : q x) :
    Fintype.equivFinOfCardEq hp ⟨x,hx⟩ = Fintype.equivFinOfCardEq hq ⟨x,hy⟩ := by
  subst q
  have hd : dq = dp := Subsingleton.elim _ _
  subst dq
  rfl

omit [Fintype C] [DecidableEq C] in
omit [DecidableEq S] in
lemma oddFrame_parity_congr (w v : Words (S := S) odd k)
    (hp : ∀ x, odd (w.1 x) ↔ odd (v.1 x)) (x : S)
    (hx : odd (w.1 x)) (hv : odd (v.1 x)) :
    oddFrame w ⟨x,hx⟩ = oddFrame v ⟨x,hv⟩ := by
  exact frame_pred_congr _ _ w.2 v.2 (funext fun x => propext (hp x)) x hx hv

omit [Fintype C] [DecidableEq C] [DecidableEq S] in
lemma oddPerm_parity_congr (g : Equiv.Perm S) (w v : Words (S := S) odd k)
    (hp : ∀ x, odd (w.1 x) ↔ odd (v.1 x)) : oddPerm g w = oddPerm g v := by
  apply Equiv.ext
  intro i
  have he : ((oddFrame w).symm i).val = ((oddFrame v).symm i).val := by
    have hh := oddFrame_parity_congr w v hp ((oddFrame w).symm i).val
      ((oddFrame w).symm i).property ((hp _).mp ((oddFrame w).symm i).property)
    rw [Equiv.apply_symm_apply] at hh
    have ht := congrArg (fun z => ((oddFrame v).symm z).val) hh
    simpa using ht.symm
  have ha : ∀ x, odd ((actWord g w).1 x) ↔ odd ((actWord g v).1 x) := fun x => hp _
  change oddFrame (actWord g w) ⟨g ((oddFrame w).symm i).val, _⟩ =
    oddFrame (actWord g v) ⟨g ((oddFrame v).symm i).val, _⟩
  have hw : odd ((actWord g w).1 (g ((oddFrame w).symm i).val)) := by
    simpa using ((oddFrame w).symm i).property
  calc
    _ = oddFrame (actWord g v) ⟨g ((oddFrame w).symm i).val, (ha _).mp hw⟩ :=
      oddFrame_parity_congr _ _ ha _ _ _
    _ = _ := congrArg (oddFrame (actWord g v)) (Subtype.ext (congrArg g he))
end RowColumn.Signed

noncomputable section
namespace RowColumn.FiniteStarAlgebra
variable {R A G : Type*} [CommSemiring R] [StarRing R] [Ring A] [Algebra R A]
  [StarRing A] [StarModule R A] [Group G]

lemma unitarySpan_eq_span (u : G →* unitary A) :
    (unitarySpan (R := R) u).toSubmodule = Submodule.span R (Set.range fun g : G => (u g : A)) := by
  apply Algebra.adjoin_eq_span_of_subset
  intro a ha
  have hh : a ∈ Set.range (fun g : G => (u g : A)) := by
    induction ha using Submonoid.closure_induction with
    | mem a ha => exact ha
    | one => exact ⟨1,by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨g,rfl⟩ := iha
      obtain ⟨h,rfl⟩ := ihb
      exact ⟨g*h,by simp⟩
  exact Submodule.subset_span hh

end RowColumn.FiniteStarAlgebra

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
open ComplexConjugate

noncomputable section
open scoped BigOperators Classical

namespace RowColumn.MatrixState
open Signed WordOrbits Postselection FiniteStarAlgebra
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  (odd : C → Prop) [DecidablePred odd] (k : ℕ)

lemma sectorUnitary_apply (U : unitary (evenAlgebra odd)) :
    (sectorUnitary (S := S) odd k U : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) =
      (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTensor odd k (fun _ : S => U.val.val)) := rfl

end RowColumn.MatrixState

namespace RowColumn.MatrixState
open Signed WordOrbits Postselection FiniteStarAlgebra
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  (odd : C → Prop) [DecidablePred odd] (k : ℕ)

omit [DecidableEq S] in
lemma sectorTensor_type_expansion (M : Matrix C C ℂ) :
    sectorTensor odd k (fun _ : S => M) =
      ∑ q : GlobalTypes (S := S) (C := C),
        typeAmplitude (fun c : C × C => M c.1 c.2) q • sectorTypeMatrix odd k q := by
  ext w v
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sectorTypeMatrix]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact prod_by_counts (fun i => (w.1 i,v.1 i)) (fun c : C × C => M c.1 c.2)

lemma sectorAlgebra_le_type_span : (sectorAlgebra (S := S) odd k).toSubmodule ≤
    Submodule.span ℂ (Set.range fun q : GlobalTypes (S := S) (C := C) =>
      (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTypeMatrix odd k q)) := by
  rw [sectorAlgebra, unitarySpan_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨U,rfl⟩
  dsimp only
  rw [sectorUnitary_apply, sectorTensor_type_expansion]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro q _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q,rfl⟩)

/-- Polynomial Fourier algebra dimension, counted by joint word types.
No representation-theoretic carrier-dimension estimate is assumed. -/
theorem sectorAlgebra_finrank : Module.finrank ℂ (sectorAlgebra (S := S) odd k) ≤
    (Fintype.card S+1)^(Fintype.card C^2) := by
  have hh := Submodule.finrank_mono (sectorAlgebra_le_type_span (S := S) odd k)
  have hc := finrank_range_le_card (R := ℂ) (fun q : GlobalTypes (S := S) (C := C) =>
    (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTypeMatrix odd k q))
  exact hh.trans (by simpa only [Set.finrank, GlobalTypes, Types, CountIndex, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_prod, pow_two] using hc)

end RowColumn.MatrixState

end
end
end
end
end
end

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator
namespace RowColumn.MatrixState
open Signed FiniteStarAlgebra
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ)

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma sectorTensor_transport (M : Matrix C C ℂ) (g : Equiv.Perm S) (w v : Words (S := S) odd k) :
    sectorTensor odd k (fun _ : S => M) (actWord g w) (actWord g v) =
      sectorTensor odd k (fun _ : S => M) w v := by
  change (∏ i, M (w.1 (g⁻¹ i)) (v.1 (g⁻¹ i))) = ∏ i, M (w.1 i) (v.1 i)
  exact Equiv.prod_comp g.symm (fun i => M (w.1 i) (v.1 i))

lemma matrix_wordVector (M : Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ)
    (w v : Words (S := S) odd k) :
    Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ) M (wordVector v) w = M w v := by
  change (∑ z, M w z * (if z=v then 1 else 0)) = M w v
  simp

lemma tensor_commutes_signed (M : Matrix C C ℂ) (heven : M ∈ evenAlgebra odd)
    (g : Equiv.Perm S) (x : Sector (S := S) odd k) :
    Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)
      (sectorTensor odd k (fun _ : S => M)) (representation g x) =
    representation g (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)
      (sectorTensor odd k (fun _ : S => M)) x) := by
  let T := Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)
      (sectorTensor odd k (fun _ : S => M))
  have hv (v : Words (S := S) odd k) : T (representation g (wordVector v)) = representation g (T (wordVector v)) := by
    ext z
    obtain ⟨w,rfl⟩ := (wordsEquiv g).surjective z
    change T (representation g (wordVector v)) (actWord g w) = representation g (T (wordVector v)) (actWord g w)
    rw [signedMap_wordVector, map_smul, signedMap_transport_apply]
    change CubeShuffle.Specht.permSign (oddPerm g v) * T (wordVector (actWord g v)) (actWord g w) =
      CubeShuffle.Specht.permSign (oddPerm g w) * T (wordVector v) w
    dsimp only [T]
    rw [matrix_wordVector, matrix_wordVector, sectorTensor_transport]
    by_cases hp : ∀ i, odd (w.1 i) ↔ odd (v.1 i)
    · rw [oddPerm_parity_congr g w v hp]
    · have hz : sectorTensor odd k (fun _ : S => M) w v=0 :=
        tensorMatrix_even_support odd _ (fun _ => heven) w.1 v.1 hp
      rw [hz, mul_zero, mul_zero]
  change T (representation g x) = representation g (T x)
  rw [← sum_wordVectors x]
  simp only [map_sum, map_smul, hv]

/-- The polynomial-dimensional tensor algebra commutes with the genuine
signed permutation representation, with no commutant-duality assumption. -/
theorem sectorAlgebra_commutes (a : sectorAlgebra (S := S) odd k)
    (g : Equiv.Perm S) (x : Sector (S := S) odd k) :
    (a : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) (representation g x) = representation g ((a : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) x) := by
  have ha := a.property
  change (a : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) ∈
    (unitarySpan (R := ℂ) (sectorUnitary (S := S) odd k)).toSubmodule at ha
  rw [unitarySpan_eq_span] at ha
  suffices hh : ∀ b ∈ Submodule.span ℂ
      (Set.range fun U => ((sectorUnitary (S := S) odd k U).val : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k)),
      b (representation g x) = representation g (b x) from hh _ ha
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨U,rfl⟩ := hb
    dsimp only
    rw [sectorUnitary_apply]
    exact tensor_commutes_signed odd k U.val.val U.val.property g x
  | zero => simp
  | add b c hb hc ihb ihc => simp only [add_apply, map_add, ihb, ihc]
  | smul z b hb ih => simp only [smul_apply, map_smul, ih]
end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_HookIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState

 theorem exists_hook_isometry (a : YoungDiagram) (h : ℕ) (H : InHook a h) :
    ∃ K : hilbertSpace a →ₗᵢ[ℂ] Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H),
      ∀ g x, K (unitaryRepresentation a g x) = HookModel.hookRepresentation a h H g (K x) := by

  let := unitaryRepresentation_irreducible a

  let f : Representation.IntertwiningMap (unitaryRepresentation a) (HookModel.hookRepresentation a h H) :=
    (HookModel.hookEmbedding a h H).comp (unitaryEquiv a).symm.toIntertwiningMap

  have hf : Function.Injective f := by
    intro x y hxy
    apply (spaceHilbertEquiv a).symm.injective
    apply HookModel.hookEmbedding_injective a h H
    exact hxy

  have hu : IsUnitary (V := Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H)) (HookModel.hookRepresentation a h H) :=
    Signed.representation_unitary (S := Cell a) (odd := HookModel.IsOdd (h := h)) (k := HookModel.oddCount a h H)

  have hh := @isometric_intertwiner_of_injective
    (Equiv.Perm (Cell a)) (hilbertSpace a)
    (Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (unitaryRepresentation a) (HookModel.hookRepresentation a h H)
    (unitaryRepresentation_unitary a) hu (unitaryRepresentation_irreducible a) f hf

  exact hh

section LineCopy
variable {S L V : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {u : ℕ} (a : YoungDiagram) (e : S ≃ Cell a) (h : ℕ) (H : InHook a h)
    (K : hilbertSpace a →ₗᵢ[ℂ] Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))
    (hK : ∀ g x, K (unitaryRepresentation a g x) = HookModel.hookRepresentation a h H g (K x))
    (line : S → L) (ρ : Representation ℂ (lineGroup line) V) (hρ : IsUnitary ρ)
    (I : Fin u → V →ₗᵢ[ℂ] hilbertSpace a)
    (hI : ∀ i, Intertwines (V := V) (W := hilbertSpace a) ρ ((relabelledUnitary a e).comp (lineGroup line).subtype) (I i).toLinearMap)

include hK hρ hI in
omit [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L] in
lemma hook_copy_projection_intertwines :
    Intertwines (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h))
      (k := HookModel.oddCount a h H) (line ∘ e.symm))
      (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h))
        (k := HookModel.oddCount a h H) (line ∘ e.symm))
      (copyProjection (fun i => K.comp (I i))).toLinearMap := by
  let τ := hookLineTarget line a e h H
  have hKI : ∀ i, Intertwines ρ τ (K.comp (I i)).toLinearMap := by
    intro i g x
    change K (I i (ρ g x)) = HookModel.hookRepresentation a h H (e.permCongr g.1) (K (I i x))
    have hi : I i (ρ g x)=unitaryRepresentation a (e.permCongr g.1) (I i x) := hI i g x
    rw [hi]
    exact hK (e.permCongr g.1) _
  have hp := copyProjection_intertwines ρ τ hρ
    (fun g => Signed.representation_unitary (e.permCongr g.1)) (fun i => K.comp (I i)) hKI
  intro g x
  have hh := hp ((lineGroupCongr e line).symm g) x
  change copyProjection (fun i => K.comp (I i))
    (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h)) (k := HookModel.oddCount a h H)
      (line ∘ e.symm) ((lineGroupCongr e line) ((lineGroupCongr e line).symm g)) x) =
    Signed.lineRepresentation (odd := HookModel.IsOdd (h := h)) (k := HookModel.oddCount a h H)
      (line ∘ e.symm) ((lineGroupCongr e line) ((lineGroupCongr e line).symm g))
      (copyProjection (fun i => K.comp (I i)) x) at hh
  rw [MulEquiv.apply_symm_apply] at hh
  exact hh

end LineCopy

section Filter
variable {G V E X : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]

omit [FiniteDimensional ℂ X] in
lemma isotypic_filter_copy_projection (ρ : Representation ℂ G X) (τ : Representation ℂ G E)
    (K : X →ₗᵢ[ℂ] E) (hK : ∀ g x, K (ρ g x)=τ g (K x))
    (Q : E →L[ℂ] E) (hQ : ∀ x ∈ Isotypic.carrier ρ τ, Q x=x)
    {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] X) :
    Q * copyProjection (fun i => K.comp (I i)) = copyProjection (fun i => K.comp (I i)) := by
  let f : Representation.IntertwiningMap ρ τ :=
    { toLinearMap := K.toLinearMap
      isIntertwining' g := by ext x; exact hK g x }
  have hk (x : X) : Q (K x)=K x := hQ _ (Isotypic.mem_carrier ρ τ f x)
  ext x
  simp only [mul_apply_eq_comp, copyProjection, sum_apply,
    map_sum, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.coe_comp, Function.comp_apply, hk]

end Filter
end RowColumn

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_TensorFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {I : Type*} [Fintype I] [DecidableEq I]

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

/-- The filter used above exists in the concrete tensor algebra, for every
actual irreducible that occurs. The identity condition on its isotypic carrier
will be applied to the explicit isometric hook embedding. -/
theorem exists_sector_isotypic_filter {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (ρ : Representation ℂ (Equiv.Perm S) V) [Representation.IsIrreducible ρ] :
    ∃ q : sectorAlgebra (S := S) odd k, star q=q ∧ q*q=q ∧ (∀ a, q*a=a*q) ∧
      (∀ x ∈ Isotypic.carrier ρ (Signed.representation (S := S) (odd := odd) (k := k)), q.val x=x) ∧
      ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
        ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / Module.finrank ℂ V :=
  exists_isotypic_filter ρ (Signed.representation (S := S) (odd := odd) (k := k))
    (Signed.representation_unitary (S := S) (odd := odd) (k := k)) (sectorAlgebra (S := S) odd k)
    (sectorAlgebra_commutes odd k)

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_OverlapBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.Signed
open MatrixState
variable {S C L K : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K]
    {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_toCLM (l : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (intertwinerMatrix l T) = T.toLinearMap.toContinuousLinearMap :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_trace (l : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l)) :
    (intertwinerMatrix l T).trace =
      LinearMap.trace ℂ (EuclideanSpace ℂ (Words (S := S) odd k)) T.toLinearMap := by
  rw [← trace_toEuclideanCLM, intertwinerMatrix_toCLM]
  rfl

omit [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
lemma intertwinerMatrix_product_trace (l : S → L) (r : S → K)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l))
    (U : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) r)
      (lineRepresentation (odd := odd) (k := k) r)) :
    (intertwinerMatrix l T * intertwinerMatrix r U).trace =
      LinearMap.trace ℂ (EuclideanSpace ℂ (Words (S := S) odd k)) (T.toLinearMap.comp U.toLinearMap) := by
  rw [← trace_toEuclideanCLM, map_mul, intertwinerMatrix_toCLM, intertwinerMatrix_toCLM]
  rfl

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_filtered (l : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l))
    (q : sectorAlgebra (S := S) odd k)
    (h : q.val * T.toLinearMap.toContinuousLinearMap=T.toLinearMap.toContinuousLinearMap) :
    algebraMatrix (sectorAlgebra (S := S) odd k) q * intertwinerMatrix l T=intertwinerMatrix l T := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ)).injective
  rw [map_mul]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ)) (algebraMatrix (sectorAlgebra (S := S) odd k) q) *
    (Matrix.toEuclideanCLM (𝕜 := ℂ)) (intertwinerMatrix l T) =
    (Matrix.toEuclideanCLM (𝕜 := ℂ)) (intertwinerMatrix l T)
  rw [intertwinerMatrix_toCLM]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ)) ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm q.val) * _ = _
  rw [StarAlgEquiv.apply_symm_apply]
  exact h

end RowColumn.Signed

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState FiniteStarAlgebra

variable {S L R V W : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R] [Nonempty S]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [DecidableEq S] in
/-- Actual hook-Specht all-copy overlap, with the concrete polynomial factors
before absorption into the one absolute constant. Orthogonality and completeness
are used later to bound the copy counts, not silently discarded from the main. -/
theorem actual_copy_overlap_bound (board : S ↪ L × R)
    (a : YoungDiagram) (e : S ≃ Cell a) (h : ℕ) (H : InHook a h) (c₀ : HookModel.Color h)
    {u v : ℕ}
    (ρ : Representation ℂ (lineGroup (fun i => (board i).1)) V)
    (τ : Representation ℂ (lineGroup (fun i => (board i).2)) W)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (I : Fin u → V →ₗᵢ[ℂ] hilbertSpace a) (J : Fin v → W →ₗᵢ[ℂ] hilbertSpace a)
    (hI : ∀ i, Intertwines (V := V) (W := hilbertSpace a) ρ
      ((relabelledUnitary a e).comp (lineGroup (fun i => (board i).1)).subtype) (I i).toLinearMap)
    (hJ : ∀ j, Intertwines (V := W) (W := hilbertSpace a) τ
      ((relabelledUnitary a e).comp (lineGroup (fun i => (board i).2)).subtype) (J j).toLinearMap) :
    allCopyOverlap (V := V) (W := W) (X := hilbertSpace a) I J ≤
      16 * (lineCost (S := Cell a) (C := HookModel.Color h) (L := L) : ℝ)^3 *
        (lineCost (S := Cell a) (C := HookModel.Color h) (L := R) : ℝ)^3 *
        (Module.finrank ℂ (sectorAlgebra (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H)) : ℝ)^2 *
        Real.exp ((Fintype.card L * Fintype.card R - Fintype.card S : ℕ) : ℝ) *
        (u * Module.finrank ℂ V : ℕ) * (v * Module.finrank ℂ W : ℕ) /
        Module.finrank ℂ (space a) := by
  let : Nonempty (Cell a) := ⟨e (Classical.choice (inferInstance : Nonempty S))⟩
  let := unitaryRepresentation_irreducible a
  obtain ⟨K,hK⟩ := exists_hook_isometry a h H
  let odd := HookModel.IsOdd (h := h)
  let k := HookModel.oddCount a h H
  let eb : Cell a ↪ L × R := e.symm.toEmbedding.trans board
  let KI := fun i => K.comp (I i)
  let KJ := fun j => K.comp (J j)
  have hr := hook_copy_projection_intertwines a e h H K hK (fun i => (board i).1) ρ hρ I hI
  have hc := hook_copy_projection_intertwines a e h H K hK (fun i => (board i).2) τ hτ J hJ
  let A : Representation.IntertwiningMap
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).1))
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).1)) :=
    { toLinearMap := (copyProjection KI).toLinearMap
      isIntertwining' g := by apply LinearMap.ext; intro x; exact hr g x }
  let B : Representation.IntertwiningMap
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).2))
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).2)) :=
    { toLinearMap := (copyProjection KJ).toLinearMap
      isIntertwining' g := by apply LinearMap.ext; intro x; exact hc g x }
  have hAp : A.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mpr (copyProjection_positive KI)
  have hBp : B.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mpr (copyProjection_positive KJ)

  obtain ⟨q,hqs,hqq,hqc,hq,hfilter⟩ := exists_sector_isotypic_filter
    (V := hilbertSpace a) odd k (unitaryRepresentation a)

  rw [finrank_hilbertSpace] at hfilter
  have hd : (0 : ℝ) < Module.finrank ℂ (space a) := by
    have hdim : 0 < Module.finrank ℂ (space a) :=
      Submodule.one_le_finrank_iff.mpr (space_ne_bot a)
    exact_mod_cast hdim

  have filterCopies := isotypic_filter_copy_projection (G := Equiv.Perm (Cell a)) (V := V)
      (E := Sector (S := Cell a) odd k) (X := hilbertSpace a) (unitaryRepresentation a)
      (Signed.representation (S := Cell a) (odd := odd) (k := k)) K
  have filterCopiesIntertwining := filterCopies hK
  have filterCopiesOperator := filterCopiesIntertwining q.val
  have filterCopiesCarrier := filterCopiesOperator hq (u := u)
  have hKI := filterCopiesCarrier I
  have hA : A.toLinearMap.toContinuousLinearMap = copyProjection KI := by
    ext x
    rfl
  have hQA := intertwinerMatrix_filtered (fun i => (eb i).1) A q (by
    rw [hA]
    exact hKI)

  have filterColumnCopies := isotypic_filter_copy_projection (G := Equiv.Perm (Cell a)) (V := W)
      (E := Sector (S := Cell a) odd k) (X := hilbertSpace a) (unitaryRepresentation a)
      (Signed.representation (S := Cell a) (odd := odd) (k := k)) K
  have filterColumnIntertwining := filterColumnCopies hK
  have filterColumnOperator := filterColumnIntertwining q.val
  have filterColumnCarrier := filterColumnOperator hq (u := v)
  have hKJ := filterColumnCarrier J
  have hB : B.toLinearMap.toContinuousLinearMap = copyProjection KJ := by
    ext x
    rfl
  have hQB := intertwinerMatrix_filtered (fun i => (eb i).2) B q (by
    rw [hB]
    exact hKJ)


  have hh := occupied_commutant_trace odd k eb (fun _ => (c₀,c₀)) A B hAp hBp
    q hqs hqq hqc (Module.finrank ℂ (space a)) hd hfilter hQA hQB

  have hAt : (intertwinerMatrix (fun i => (eb i).1) A).trace = (u * Module.finrank ℂ V : ℕ) := by
    rw [intertwinerMatrix_trace]
    exact copyProjection_trace KI
  have hBt : (intertwinerMatrix (fun i => (eb i).2) B).trace = (v * Module.finrank ℂ W : ℕ) := by
    rw [intertwinerMatrix_trace]
    exact copyProjection_trace KJ
  rw [intertwinerMatrix_product_trace, hAt, hBt] at hh
  have hcard : Fintype.card (Cell a)=Fintype.card S := (Fintype.card_congr e).symm
  simp only [Complex.natCast_re, hcard] at hh
  have hinv := allCopyOverlap_comp_isometry (V := V) (W := W) (X := hilbertSpace a)
    (E := Sector (S := Cell a) odd k) I J K
  calc _ = allCopyOverlap (V := V) (W := W) (X := Sector (S := Cell a) odd k) KI KJ := hinv.symm
       _ ≤ _ := (allCopyOverlap_le_trace (V := V) (W := W)
         (X := Sector (S := Cell a) odd k) KI KJ).trans hh

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

lemma occupied_factor_bound (s m n h u v D : ℕ) (t : ℝ)
    (hu : u ≤ (s+1)^(4*m*h^2)) (hv : v ≤ (s+1)^(4*n*h^2))
    (hD : D ≤ (s+1)^(4*h^2)) :
    16 * ((s+1 : ℕ) : ℝ)^(4*m*h^2*3) * ((s+1 : ℕ) : ℝ)^(4*n*h^2*3) *
      (D : ℝ)^2 * Real.exp t * u * v ≤
    16 * ((s : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp t := by
  have hu' : (u : ℝ) ≤ ((s : ℝ)+1)^(4*m*h^2) := by exact_mod_cast hu
  have hv' : (v : ℝ) ≤ ((s : ℝ)+1)^(4*n*h^2) := by exact_mod_cast hv
  have hD' : (D : ℝ) ≤ ((s : ℝ)+1)^(4*h^2) := by exact_mod_cast hD
  calc
    _ ≤ 16 * ((s : ℝ)+1)^(4*m*h^2*3) * ((s : ℝ)+1)^(4*n*h^2*3) *
      (((s : ℝ)+1)^(4*h^2))^2 * Real.exp t * ((s : ℝ)+1)^(4*m*h^2) *
      ((s : ℝ)+1)^(4*n*h^2) := by
        push_cast
        gcongr
    _ = _ := by
      rw [show (16*(m+n)+8)*h^2 = 4*m*h^2*3 + 4*n*h^2*3 + (4*h^2)*2 + 4*m*h^2 + 4*n*h^2 by ring]
      simp only [pow_add, pow_mul]
      ring

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.Specht Signed MatrixState

lemma hook_lineCost {S L : Type*} [Fintype S] [Fintype L] (h : ℕ) :
    lineCost (S := S) (C := HookModel.Color h) (L := L) =
      (Fintype.card S+1)^(4*Fintype.card L*h^2) := by
  simp only [lineCost, HookModel.Color, Fintype.card_sum, Fintype.card_fin]
  congr 1
  ring

lemma hook_sectorAlgebra_bound {S : Type*} [Fintype S] [DecidableEq S] (h k : ℕ) :
    Module.finrank ℂ (sectorAlgebra (S := S) (HookModel.IsOdd (h := h)) k) ≤
      (Fintype.card S+1)^(4*h^2) := by
  have hh := sectorAlgebra_finrank (S := S) (HookModel.IsOdd (h := h)) k
  simpa only [HookModel.Color, Fintype.card_sum, Fintype.card_fin, show (h+h)^2=4*h^2 by ring] using hh

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState

/-- The dimension-ratio half of the occupied main, now for the literal occupied
subset and all prescribed row and column embeddings. -/
theorem occupied_dimension_ratio_oai (m n : ℕ) (Ω : Finset (Board m n)) [Nonempty Ω]
    (a : YoungDiagram) (e : Ω ≃ Cell a) (h : ℕ) (hh : 1 ≤ h) (H : InHook a h)
    (r c u v : ℕ)
    (ρ : Representation ℂ (rowGroup Ω) (EuclideanSpace ℂ (Fin r)))
    (τ : Representation ℂ (columnGroup Ω) (EuclideanSpace ℂ (Fin c)))
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (I : Fin u → EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] hilbertSpace a)
    (J : Fin v → EuclideanSpace ℂ (Fin c) →ₗᵢ[ℂ] hilbertSpace a)
    (hI : ∀ i, Intertwines (V := EuclideanSpace ℂ (Fin r)) (W := hilbertSpace a)
      ρ ((relabelledUnitary a e).comp (rowGroup Ω).subtype) (I i).toLinearMap)
    (hJ : ∀ i, Intertwines (V := EuclideanSpace ℂ (Fin c)) (W := hilbertSpace a)
      τ ((relabelledUnitary a e).comp (columnGroup Ω).subtype) (J i).toLinearMap)
    (hu : u ≤ (Ω.card+1)^(4*m*h^2)) (hv : v ≤ (Ω.card+1)^(4*n*h^2)) :
    allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤
      (16 * ((Ω.card : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp ((m*n-Ω.card : ℕ) : ℝ)) *
        ((r : ℝ)*c / Module.finrank ℂ (space a)) := by
  let board : Ω ↪ Fin m × Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  let c₀ : HookModel.Color h := Sum.inl ⟨0, by omega⟩
  have ha := actual_copy_overlap_bound (V := EuclideanSpace ℂ (Fin r))
    (W := EuclideanSpace ℂ (Fin c)) board a e h H c₀ ρ τ hρ hτ I J hI hJ
  have hc : Fintype.card (Cell a) = Ω.card := (Fintype.card_congr e).symm.trans (Fintype.card_coe Ω)
  have hD := hook_sectorAlgebra_bound (S := Cell a) h (HookModel.oddCount a h H)
  rw [hc] at hD
  let D := Module.finrank ℂ (sectorAlgebra (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))
  have hp := occupied_factor_bound Ω.card m n h u v D ((m*n-Ω.card : ℕ) : ℝ) hu hv hD
  have hratio : 0 ≤ (r : ℝ)*c / (Module.finrank ℂ (space a) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hp hratio
  simp only [hook_lineCost, hc, Fintype.card_fin, Fintype.card_coe, finrank_euclideanSpace,
    Nat.cast_mul, Nat.cast_pow, ← pow_mul] at ha
  apply ha.trans
  convert hmul using 1; dsimp [D]; ring

end RowColumn

end
end


end OAI
end

theorem solution : type_of% @OAI.RowColumn.occupied_dimension_ratio_oai := @OAI.RowColumn.occupied_dimension_ratio_oai
