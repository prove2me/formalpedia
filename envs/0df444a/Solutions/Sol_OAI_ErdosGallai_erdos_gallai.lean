-- Prove2me | solution 1 for OAI.ErdosGallai.erdos_gallai
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:08:46.985674+00:00
-- url     : https://prove2.me/submissions/ae0311ab-7f08-470d-b9c5-ec6691e37c40

import Mathlib
import Definitions.Def_CycleDecomposition
import Definitions.Def_OAIQWEGC000
import Theorems.Thm_OAI_ErdosGallai_Scale_long_cycle_of_expansion
import Theorems.Thm_OAI_ErdosGallai_Scale_uniform_committed_piece_cost
import Theorems.Thm_OAI_ErdosGallai_Scale_uniform_local_box_cost

section
-- module Solutions.OAIQW_ErdosGallai.Compat
namespace OAI.ErdosGallai
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434


end OAI.ErdosGallai
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Real Filter Asymptotics

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

noncomputable section
open SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

lemma decompositionCost_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G ≤ Nat.card G.edgeSet := decompositionCost_le (edgeDecomposition_singleEdges G)

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

lemma decompositionCost_assemble_same {V J : Type} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ ∑ j, decompositionCost (H j) := by
  simpa using decompositionCost_adjoin_same (I := Empty) G Empty.elim (fun i => nomatch i)
    (by intro i; exact i.elim) H hHG hHH (fun _ i => nomatch i) (by simpa using hu)

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CycleLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Real Filter Asymptotics

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CoupledResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Batch
noncomputable section
open Real

lemma inductionPhi_one : inductionPhi 1 = 1/2 := by simp [inductionPhi]

lemma inductionPhi_bounds (x : ℝ) : 1/2 ≤ inductionPhi x ∧ inductionPhi x ≤ 1 := by
  by_cases hx : x = 1
  · norm_num [inductionPhi, hx]
  · simp only [inductionPhi, hx, ite_false]
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [one_div_nonneg.mpr (Real.sqrt_nonneg (logb 2 x))])⟩

lemma inductionPhi_monotone : MonotoneOn inductionPhi (Set.Ici 1) := by
  intro x hx y hy hxy
  by_cases hx1 : x = 1
  · simpa [hx1, inductionPhi_one] using (inductionPhi_bounds y).1
  have hxgt : 1 < x := lt_of_le_of_ne hx (Ne.symm hx1)
  have hygt : 1 < y := hxgt.trans_le hxy
  have hlog : logb 2 x ≤ logb 2 y := Real.logb_le_logb_of_le (by norm_num)
    (by linarith) hxy
  have hxlog : 0 < logb 2 x := Real.logb_pos (by norm_num) hxgt
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hxlog) (Real.sqrt_le_sqrt hlog)
  simp only [inductionPhi, hx1, ne_of_gt hygt, ite_false]
  exact max_le_max le_rfl (by linarith)

lemma inductionPhi_nonconstant (x : ℝ) (hlog : 4 ≤ logb 2 x) :
    inductionPhi x = 1 - 1 / sqrt (logb 2 x) := by
  have hx : x ≠ 1 := by intro hx; subst x; norm_num at hlog
  have hsqrt : 2 ≤ sqrt (logb 2 x) := by
    convert Real.sqrt_le_sqrt hlog using 1 ; norm_num
  have hinv : 1 / sqrt (logb 2 x) ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) hsqrt
  simp only [inductionPhi, hx, ite_false]
  exact max_eq_right (by linarith)

lemma inductionDelta_pos : 0 < inductionDelta := by
  have hs : 0 < sqrt (3/10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : sqrt (3/10 : ℝ) < 1 := by
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  dsimp [inductionDelta]
  have hh := (one_lt_div hs).mpr hs1
  linarith

theorem induction_potential_gain (D n : ℝ) (hD : 1 < D) (hn : D ≤ n)
    (hw : 40/3 ≤ logb 2 D) :
    inductionDelta / sqrt (logb 2 D) ≤ inductionPhi n - inductionPhi (D^(3/10:ℝ)) := by
  have hD0 : 0 < D := by linarith
  have hw0 : 0 < logb 2 D := by linarith
  have hnlog : logb 2 D ≤ logb 2 n :=
    Real.logb_le_logb_of_le (by norm_num) hD0 hn
  have hblog : logb 2 (D^(3/10:ℝ)) = (3/10)*logb 2 D := by
    exact Real.logb_rpow_eq_mul_logb_of_pos hD0
  rw [inductionPhi_nonconstant n (by linarith),
    inductionPhi_nonconstant (D^(3/10:ℝ)) (by rw [hblog]; linarith), hblog]
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hw0)
    (Real.sqrt_le_sqrt hnlog)
  have hid : 1 / sqrt ((3/10)*logb 2 D) - 1 / sqrt (logb 2 D) =
    inductionDelta / sqrt (logb 2 D) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/10)]
    dsimp [inductionDelta]
    field_simp
  rw [← hid]
  linarith

lemma induction_cutoff_absorption (A w : ℝ) (hA : 0 ≤ A) (hw0 : 0 < w)
    (hw : ((A+1)/inductionDelta)^2 ≤ w) :
    (A+1)/w ≤ inductionDelta / sqrt w := by
  have hd := inductionDelta_pos
  have hratio : 0 ≤ (A+1)/inductionDelta := by positivity
  have hs : (A+1)/inductionDelta ≤ sqrt w := by
    have hh := Real.sqrt_le_sqrt hw
    simpa [Real.sqrt_sq hratio] using hh
  have hm : A+1 ≤ inductionDelta * sqrt w := by
    have := (div_le_iff₀ hd).mp hs
    simpa [mul_comm] using this
  apply (div_le_div_iff₀ hw0 (Real.sqrt_pos.mpr hw0)).mpr
  have hmul := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg w)
  simpa [mul_assoc, Real.mul_self_sqrt hw0.le] using hmul

theorem induction_cost_absorbed (D n S C A₁ A₂ : ℝ)
    (hD : 1 < D) (hn : D ≤ n) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hA₁ : 0 ≤ A₁) (_hA₂ : 0 ≤ A₂) (hCA : 7*A₂ ≤ C)
    (hw : 40/3 ≤ logb 2 D)
    (hcut : ((A₁+1)/inductionDelta)^2 ≤ logb 2 D) :
    A₂*(S+n/logb 2 D) + (C/100)*S +
      C*inductionPhi (D^(3/10:ℝ))*(n-S/3+A₁*n/logb 2 D) ≤ C*inductionPhi n*n := by
  let f := inductionPhi (D^(3/10:ℝ))
  obtain ⟨hflo,hfhi⟩ := inductionPhi_bounds (D^(3/10:ℝ))
  have hw0 : 0 < logb 2 D := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hnw : 0 ≤ n/logb 2 D := div_nonneg hn0 hw0.le
  have hcoeff : A₂+C/100-C*f/3 ≤ 0 := by
    dsimp [f]
    nlinarith [mul_le_mul_of_nonneg_left hflo hC]
  have hScost := mul_nonpos_of_nonpos_of_nonneg hcoeff hS
  have hA₂C : A₂ ≤ C := by linarith
  have hAprod : C*f*A₁ ≤ C*A₁ := by
    exact mul_le_mul_of_nonneg_right (by
      simpa [f] using mul_le_mul_of_nonneg_left hfhi hC) hA₁
  have how := mul_le_mul_of_nonneg_right (add_le_add hA₂C hAprod) hnw
  have habs := induction_cutoff_absorption A₁ (logb 2 D) hA₁ hw0 hcut
  have hgain := induction_potential_gain D n hD hn hw
  have hpay := mul_le_mul_of_nonneg_left (habs.trans hgain) (mul_nonneg hC hn0)
  change A₂*(S+n/logb 2 D) + (C/100)*S + C*f*(n-S/3+A₁*n/logb 2 D) ≤ _
  change C*n*((A₁+1)/logb 2 D) ≤ C*n*(inductionPhi n - f) at hpay
  simp only [div_eq_mul_inv] at hScost how hpay ⊢
  nlinarith only [hScost, how, hpay]

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ExpansionBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

theorem long_cycle_of_vertex_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hexp : VertexExpansion G α)
    (hq : 1 ≤ α^2 * Fintype.card V / 100) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧
      α^2 * Fintype.card V / 100 < (c.length : ℝ) :=
  long_cycle_of_expansion G α hα hα1 hexp hq

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open Finset SimpleGraph Classical
variable {V : Type cycleUniverse5} [Fintype V] [DecidableEq V]

lemma restrictGraph_le {V : Type cycleUniverse10} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A : Finset V) : restrictGraph G A ≤ G :=
  fun _ _ h => h.1
lemma restrictGraph_supported {V : Type cycleUniverse11} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    SupportedOn (restrictGraph G A) A := fun _ _ h => h.2

lemma partition_member_le {V : Type cycleUniverse12} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) {H : SimpleGraph V} (hH : H ∈ L) : H ≤ G := by
  classical
  intro x y hxy
  by_contra hn
  have hc := h x y
  simp only [hn, ite_false] at hc
  have hp : 0 < edgeOccurrences L x y := by
    simpa [edgeOccurrences, List.countP_pos_iff] using (show ∃ K ∈ L, K.Adj x y from ⟨H,hH,hxy⟩)
  omega

open Real

lemma logb_four_thirds : (1/4:ℝ) ≤ logb 2 (4/3) := by
  have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=(4/3:ℝ)^4)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow] at h
  norm_num only [Real.logb_self_eq_one, Nat.cast_ofNat] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

lemma splitPotential_bounds (T x : ℝ) (hT : 4 ≤ T) :
    1 ≤ splitPotential T x ∧ splitPotential T x ≤ 2 := by
  have hbase : 1 ≤ logb 2 (T/2) := by
    have hh := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=T/2)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at hh
    exact hh
  have hlog := Real.logb_le_logb_of_le (b:=2) (x:=T/2) (y:=max x (T/2))
    (by norm_num) (by linarith) (le_max_right _ _)
  have hsmall : 0 < logb 2 (T/2) := by linarith
  have hbig : 0 < logb 2 (max x (T/2)) := by linarith
  have hrecip : 1 / logb 2 (max x (T/2)) ≤ 1 / logb 2 (T/2) :=
    one_div_le_one_div_of_le hsmall hlog
  have hrecipone : 1/logb 2 (T/2) ≤ 1 := (div_le_one hsmall).mpr hbase
  dsimp [splitPotential]
  constructor
  · linarith
  · linarith [one_div_pos.mpr hbig]

lemma splitPotential_monotone (T : ℝ) (hT : 4 ≤ T) : Monotone (splitPotential T) := by
  intro x y hxy
  have hpos : 0 < T/2 := by linarith
  have hlogx : 0 < logb 2 (max x (T/2)) :=
    Real.logb_pos (by norm_num) (lt_of_lt_of_le (by linarith : 1 < T/2) (le_max_right _ _))
  have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num)
    (lt_of_lt_of_le hpos (le_max_right x (T/2))) (max_le_max hxy le_rfl)
  have hi := one_div_le_one_div_of_le hlogx hlog
  dsimp [splitPotential]
  linarith

lemma split_potential_decrement (T u u₁ : ℝ) (hT : 4 ≤ T) (hu : T < u)
    (h₁ : u₁ ≤ 3*u/4) :
    (1/4:ℝ)/(logb 2 u)^2 ≤ splitPotential T u - splitPotential T u₁ := by
  let M := max u₁ (T/2)
  have hu0 : 0 < u := by linarith
  have hM0 : 0 < M := lt_of_lt_of_le (by linarith : 0 < T/2) (le_max_right _ _)
  have hMu : M ≤ 3*u/4 := max_le h₁ (by linarith)
  have hMlt : M ≤ u := by linarith
  have hLu : 0 < logb 2 u := Real.logb_pos (by norm_num) (by linarith)
  have hLM : 0 < logb 2 M := Real.logb_pos (by norm_num)
    (lt_of_lt_of_le (by linarith : 1 < T/2) (le_max_right _ _))
  have hlle : logb 2 M ≤ logb 2 u :=
    Real.logb_le_logb_of_le (by norm_num) hM0 hMlt
  have hquot : (4/3:ℝ) ≤ u/M := (le_div_iff₀ hM0).mpr (by linarith)
  have hlogq := Real.logb_le_logb_of_le (b:=2) (x:=4/3) (y:=u/M)
    (by norm_num) (by norm_num) hquot
  rw [Real.logb_div hu0.ne' hM0.ne'] at hlogq
  have hgap : (1/4:ℝ) ≤ logb 2 u - logb 2 M := logb_four_thirds.trans hlogq
  have hmax : max u (T/2) = u := max_eq_left (by linarith)
  dsimp [splitPotential]
  rw [hmax]
  change (1/4:ℝ)/(logb 2 u)^2 ≤
    (1+1/logb 2 (T/2)-1/logb 2 u) - (1+1/logb 2 (T/2)-1/logb 2 M)
  have hid : (1+1/logb 2 (T/2)-1/logb 2 u) - (1+1/logb 2 (T/2)-1/logb 2 M) =
      (logb 2 u-logb 2 M)/(logb 2 M*logb 2 u) := by field_simp; ring
  rw [hid]
  apply (div_le_div_iff₀ (sq_pos_of_pos hLu) (mul_pos hLM hLu)).mpr
  have hm := mul_le_mul_of_nonneg_right hlle hLu.le
  nlinarith [sq_nonneg (logb 2 u)]

lemma split_potential_subadditive (T u u₁ u₂ : ℝ) (hT : 4 ≤ T) (hu : T < u)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (h₁ : u₁ ≤ 3*u/4) (h₂ : u₂ ≤ u)
    (hsum : u₁+u₂ ≤ u+(1/32:ℝ)*u₁/(logb 2 u)^2) :
    u₁*splitPotential T u₁ + u₂*splitPotential T u₂ ≤ u*splitPotential T u := by
  have hdec := split_potential_decrement T u u₁ hT hu h₁
  have hmono := splitPotential_monotone T hT h₂
  obtain ⟨hfpos,hfhi⟩ := splitPotential_bounds T u hT
  have h₁cost := mul_le_mul_of_nonneg_left hdec hu₁
  have h₂cost := mul_le_mul_of_nonneg_left hmono hu₂
  have hLu : 0 < logb 2 u := Real.logb_pos (by norm_num) (by linarith)
  have hden : 0 < (logb 2 u)^2 := sq_pos_of_pos hLu
  have hsumcost := mul_le_mul_of_nonneg_right hsum (by linarith : 0 ≤ splitPotential T u)
  have hwt : 0 ≤ u₁/(logb 2 u)^2 := div_nonneg hu₁ hden.le
  have hratio : u₁*((1/4:ℝ)/(logb 2 u)^2) = (1/4:ℝ)*(u₁/(logb 2 u)^2) := by ring
  have hratio2 : ((1/32:ℝ)*u₁/(logb 2 u)^2)*splitPotential T u =
      (1/32:ℝ)*(u₁/(logb 2 u)^2)*splitPotential T u := by ring
  simp only [add_mul] at hsumcost
  rw [hratio2] at hsumcost
  rw [hratio] at h₁cost
  nlinarith

lemma externalOn_subset {G : SimpleGraph V} {A U : Finset V} (hG : SupportedOn G A) :
    externalOn G U ⊆ A := by
  intro x hx
  obtain ⟨u,hu,hadj⟩ := (Finset.mem_filter.mp hx).2.2
  exact (hG hadj).2

lemma externalOn_disjoint (G : SimpleGraph V) (U : Finset V) :
    Disjoint U (externalOn G U) := by
  apply Finset.disjoint_left.mpr
  intro x hx hn
  exact (Finset.mem_filter.mp hn).2.1 hx

lemma overlap_child_supported {G : SimpleGraph V} {A U : Finset V}
    (hG : SupportedOn G A) (_hU : U ⊆ A) :
    SupportedOn (G \ restrictGraph G (U ∪ externalOn G U)) (A\U) := by
  intro x y hxy
  obtain ⟨hx,hy⟩ := hG hxy.1
  have hb (x y : V) (hxy : G.Adj x y) (hx : x ∈ U) : y ∈ U ∪ externalOn G U := by
    by_cases hy : y ∈ U
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy,x,hx,hxy⟩)
  constructor
  · refine Finset.mem_sdiff.mpr ⟨hx,fun hxU => ?_⟩
    exact hxy.2 ⟨hxy.1,Finset.mem_union_left _ hxU,hb x y hxy.1 hxU⟩
  · refine Finset.mem_sdiff.mpr ⟨hy,fun hyU => ?_⟩
    exact hxy.2 ⟨hxy.1,hb y x hxy.1.symm hyU,Finset.mem_union_left _ hyU⟩

lemma overlap_child_sizes {G : SimpleGraph V} {A U : Finset V} {T : ℝ}
    (hT : 4 ≤ T) (hlarge : T < (A.card : ℝ)) (hU : U ⊆ A)
    (hne : U.Nonempty) (hhalf : 2*U.card ≤ A.card)
    (hsparse : ((externalOn G U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 A.card)^2) :
    (U ∪ externalOn G U).Nonempty ∧ (A\U).Nonempty ∧
    ((U ∪ externalOn G U).card : ℝ) ≤ 3*A.card/4 ∧
    (A\U).card < A.card ∧
    ((U ∪ externalOn G U).card : ℝ) + (A\U).card ≤
      A.card+(1/32:ℝ)*(U ∪ externalOn G U).card/(logb 2 A.card)^2 := by
  have hu : 0 < U.card := hne.card_pos
  have hlog : 1 ≤ logb 2 (A.card : ℝ) := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=A.card)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at h
    exact h
  have hd : 0 < (logb 2 (A.card : ℝ))^2 := by positivity
  have hquot : (1/32:ℝ)/(logb 2 (A.card : ℝ))^2 ≤ 1/2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (logb 2 (A.card : ℝ)-1)]
  have hsmall : ((externalOn G U).card : ℝ) < (U.card : ℝ)/2 := by
    have hm := mul_le_mul_of_nonneg_right hquot (Nat.cast_nonneg U.card)
    have hid : (1/32:ℝ)/(logb 2 (A.card : ℝ))^2 * U.card =
        (1/32:ℝ)*U.card/(logb 2 (A.card : ℝ))^2 := by ring
    rw [hid] at hm
    linarith
  have hcard₁ := Finset.card_union_of_disjoint (externalOn_disjoint G U)
  have hcard₂ := Finset.card_sdiff_add_card_eq_card hU
  have hcard₁R : ((U ∪ externalOn G U).card : ℝ) = U.card+(externalOn G U).card := by
    exact_mod_cast hcard₁
  have hcard₂R : ((A\U).card : ℝ) + U.card = A.card := by exact_mod_cast hcard₂
  have hhalfR : 2*(U.card : ℝ) ≤ A.card := by exact_mod_cast hhalf
  have hmon : (1/32:ℝ)*U.card/(logb 2 A.card)^2 ≤
      (1/32:ℝ)*(U ∪ externalOn G U).card/(logb 2 A.card)^2 := by
    gcongr
    exact Finset.subset_union_left
  refine ⟨hne.mono Finset.subset_union_left,?_,?_,?_,?_⟩
  · exact Finset.card_pos.mp (by omega)
  · linarith
  · omega
  · linarith

lemma partition_split_append {G K : SimpleGraph V} {L M : List (SimpleGraph V)}
    (hle : K ≤ G) (hL : GraphPartition K L) (hM : GraphPartition (G\K) M) :
    GraphPartition G (L++M) := by
  intro x y
  have h₁ := hL x y
  have h₂ := hM x y
  have hk := @hle x y
  simp only [edgeOccurrences_append,SimpleGraph.sdiff_adj] at h₂ ⊢
  by_cases hK : K.Adj x y <;> by_cases hG : G.Adj x y <;> simp_all

theorem box_recursion (G : SimpleGraph V) (A : Finset V) (T : ℝ)
    (hT : 4 ≤ T) (hA : A.Nonempty) (hG : SupportedOn G A)
    (hsplit : ∀ B ⊆ A, ∀ H : SimpleGraph V, H ≤ G → SupportedOn H B → T < (B.card : ℝ) →
      ∃ U ⊆ B, U.Nonempty ∧ 2*U.card ≤ B.card ∧
        ((externalOn H U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 B.card)^2) :
    ∃ L : List (AssignedPiece V),
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧ (P.vertices.card : ℝ) ≤ T) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      GraphPartition G (L.map AssignedPiece.graph) ∧
      (L.map (fun P => (P.vertices.card : ℝ)*splitPotential T P.vertices.card)).sum ≤
        (A.card : ℝ)*splitPotential T A.card := by
  classical
  induction hn : A.card using Nat.strong_induction_on generalizing A G with
  | h n ih =>
    by_cases hsmall : (A.card : ℝ) ≤ T
    · let P : AssignedPiece V := ⟨A,G,hG⟩
      refine ⟨[P],?_,?_,?_,?_⟩
      · intro Q hQ; simp only [List.mem_singleton] at hQ; subst Q
        exact ⟨Finset.Subset.refl _,hA,hsmall⟩
      · intro x hx; exact ⟨P,by simp,hx⟩
      · intro x y; simp [P]
      · simp [P,← hn]
    · have hlarge : T < (A.card : ℝ) := lt_of_not_ge hsmall
      obtain ⟨U,hU,hne,hhalf,hsparse⟩ := hsplit A (Finset.Subset.refl _) G le_rfl hG hlarge
      let B := externalOn G U
      let A₁ := U ∪ B
      let A₂ := A\U
      let G₁ := restrictGraph G A₁
      let G₂ := G\G₁
      have hA₁ : A₁ ⊆ A := Finset.union_subset hU (externalOn_subset hG)
      have hA₂ : A₂ ⊆ A := Finset.sdiff_subset
      have hG₁ : G₁ ≤ G := restrictGraph_le G A₁
      have hG₂ : G₂ ≤ G := sdiff_le
      have hs₁ : SupportedOn G₁ A₁ := restrictGraph_supported G A₁
      have hs₂ : SupportedOn G₂ A₂ := overlap_child_supported hG hU
      obtain ⟨hn₁,hn₂,hsize₁,hsize₂,hsum⟩ := overlap_child_sizes hT hlarge hU hne hhalf hsparse
      have hlt₁ : A₁.card < n := by
        have hn0 : (0 : ℝ) < A.card := by linarith
        have hlt : (A₁.card : ℝ) < A.card := lt_of_le_of_lt hsize₁ (by linarith)
        exact hn ▸ (Nat.cast_lt.mp hlt)
      have hlt₂ : A₂.card < n := hn ▸ hsize₂
      have subprem (D : Finset V) (hD : D ⊆ A) (K : SimpleGraph V) (hK : K ≤ G) :
          ∀ C ⊆ D, ∀ H : SimpleGraph V, H ≤ K → SupportedOn H C → T < (C.card : ℝ) →
            ∃ U ⊆ C, U.Nonempty ∧ 2*U.card ≤ C.card ∧
              ((externalOn H U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 C.card)^2 := by
        intro C hC H hH hs hlarge
        exact hsplit C (hC.trans hD) H (hH.trans hK) hs hlarge
      obtain ⟨L,hL,hcovL,hpartL,hcostL⟩ := ih _ hlt₁ G₁ A₁ hn₁ hs₁
        (subprem A₁ hA₁ G₁ hG₁) rfl
      obtain ⟨M,hM,hcovM,hpartM,hcostM⟩ := ih _ hlt₂ G₂ A₂ hn₂ hs₂
        (subprem A₂ hA₂ G₂ hG₂) rfl
      refine ⟨L++M,?_,?_,?_,?_⟩
      · intro P hP
        rcases List.mem_append.mp hP with hP | hP
        · obtain ⟨hsub,hne,hbound⟩ := hL P hP; exact ⟨hsub.trans hA₁,hne,hbound⟩
        · obtain ⟨hsub,hne,hbound⟩ := hM P hP; exact ⟨hsub.trans hA₂,hne,hbound⟩
      · intro x hx
        by_cases hxU : x ∈ U
        · obtain ⟨P,hP,hxP⟩ := hcovL x (Finset.mem_union_left _ hxU)
          exact ⟨P,List.mem_append_left _ hP,hxP⟩
        · obtain ⟨P,hP,hxP⟩ := hcovM x (Finset.mem_sdiff.mpr ⟨hx,hxU⟩)
          exact ⟨P,List.mem_append_right _ hP,hxP⟩
      · simpa only [List.map_append] using partition_split_append hG₁ hpartL hpartM
      · simp only [List.map_append,List.sum_append]
        have hsub := split_potential_subadditive T A.card A₁.card A₂.card hT hlarge
          (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsize₁ (by exact_mod_cast hsize₂.le) hsum
        rw [← hn]
        linarith

end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ScaleExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph Classical
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]
lemma edgeCount_eq_card {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : ∀ e, e ∈ S ↔ e ∈ G.edgeSet) : edgeCount G = S.card := by
  unfold edgeCount
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  exact (hS e).symm

lemma NoLongCycle.mono {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G H : SimpleGraph V} {ℓ : ℝ}
    (h : NoLongCycle G ℓ) (hle : H ≤ G) : NoLongCycle H ℓ := by
  intro a p hp
  simpa using h a (p.mapLe hle) (hp.mapLe hle)

lemma cycle_graph_of_walk (G : SimpleGraph V) {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ K : SimpleGraph V, K ≤ G ∧ IsCycleGraph K ∧ edgeCount K = p.length := by
  classical
  let K := SimpleGraph.fromEdgeSet p.edgeSet
  have he : K.edgeSet = p.edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet,sdiff_eq_left]
    exact Set.disjoint_left.mpr (fun e he hd =>
      G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he) hd)
  have hle : K ≤ G := SimpleGraph.edgeSet_subset_edgeSet.mp (he ▸ p.edges_subset_edgeSet)
  have htransfer : ∀ e ∈ p.edges, e ∈ K.edgeSet := by
    intro e he'; rw [he]; exact he'
  refine ⟨K,hle,⟨a,p.transfer K htransfer,hp.transfer htransfer,?_⟩,?_⟩
  · simpa using he
  · rw [edgeCount_eq_card K p.edges.toFinset (by
      intro e; simp only [List.mem_toFinset,he]; rfl)]
    exact (List.toFinset_card_of_nodup hp.isTrail.edges_nodup).trans p.length_edges

lemma edgeCount_sdiff_add {G K : SimpleGraph V} (hle : K ≤ G) :
    edgeCount (G \ K) + edgeCount K = edgeCount G := by
  classical
  rw [edgeCount_eq_card (G \ K) (G.edgeFinset \ K.edgeFinset) (by
    intro e; simp only [Finset.mem_sdiff,SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_sdiff,
      Set.mem_sdiff]),
    edgeCount_eq_card K K.edgeFinset (by intro e; simp),
    edgeCount_eq_card G G.edgeFinset (by intro e; simp)]
  exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hle)

lemma edgeCount_cycle_pos {K : SimpleGraph V} (h : IsCycleGraph K) : 0 < edgeCount K := by
  classical
  obtain ⟨a,p,hp,he⟩ := h
  have hf : K.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset,he,List.mem_toFinset]
    rfl
  simp only [edgeCount,hf,List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
    SimpleGraph.Walk.length_edges]
  exact hp.three_le_length.trans_lt' (by omega)

theorem remove_long_cycles (G : SimpleGraph V) (ℓ : ℝ) :
    ∃ (H : SimpleGraph V) (L : List (SimpleGraph V)),
      H ≤ G ∧ NoLongCycle H ℓ ∧
      (∀ K ∈ L, IsCycleGraph K ∧ ℓ ≤ (edgeCount K : ℝ)) ∧
      GraphPartition G (H::L) ∧
      (L.length : ℝ)*ℓ + edgeCount H ≤ edgeCount G := by
  classical
  induction hn : edgeCount G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hstop : NoLongCycle G ℓ
    · refine ⟨G,[],le_rfl,hstop,by simp,?_,?_⟩
      · intro x y; simp
      · simp [← hn]
    · obtain ⟨a,p,hp,hplen⟩ : ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ℓ ≤ (p.length : ℝ) := by
        by_contra hh
        apply hstop
        intro a p hp
        by_contra hlen
        exact hh ⟨a,p,hp,le_of_not_gt hlen⟩
      obtain ⟨K,hle,hK,hKlen⟩ := cycle_graph_of_walk G p hp
      have heq := edgeCount_sdiff_add hle
      have hpos := edgeCount_cycle_pos hK
      have hlt : edgeCount (G \ K) < n := by omega
      obtain ⟨H,L,hH,hNL,hL,hpart,hbudget⟩ := ih _ hlt (G \ K) rfl
      refine ⟨H,K::L,hH.trans sdiff_le,hNL,?_,?_,?_⟩
      · intro J hJ
        rcases List.mem_cons.mp hJ with rfl | hJ
        · exact ⟨hK,by simpa [hKlen] using hplen⟩
        · exact hL J hJ
      · intro x y
        have hh := @hH x y
        have hk := @hle x y
        have he := hpart x y
        simp only [edgeOccurrences_cons,SimpleGraph.sdiff_adj] at he ⊢
        by_cases hG : G.Adj x y <;> by_cases hK : K.Adj x y <;>
          by_cases hH : H.Adj x y <;> simp_all
      · have heqR : (edgeCount (G \ K) : ℝ) + edgeCount K = edgeCount G := by exact_mod_cast heq
        have hKbound : ℓ ≤ (edgeCount K : ℝ) := by simpa [hKlen] using hplen
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        rw [← hn]
        nlinarith

open Real Filter Asymptotics

lemma longCycle_power_margin : ∀ᶠ u : ℝ in atTop,
    4 ≤ u ∧ u^(199/200:ℝ) ≤ ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ)
    (s:=1/200) (by norm_num)).const_mul_left ((102400:ℝ)/(log 2)^4)
  filter_upwards [eventually_ge_atTop (4:ℝ),hlog.eventuallyLE] with u hu hh
  have hu0 : 0 < u := by linarith
  have hln : 0 ≤ log u := log_nonneg (by linarith)
  have hln2 : 0 < log 2 := log_pos (by norm_num)
  have hLu : 0 < logb 2 u := logb_pos (by norm_num) (by linarith)
  have hr0 : 0 ≤ u^(1/200:ℝ) := rpow_nonneg hu0.le _
  have hnum0 : 0 ≤ (102400:ℝ)/(log 2)^4 * (log u)^(4:ℝ) := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hnum0,abs_of_nonneg hr0] at hh
  have hden : (102400:ℝ)*(logb 2 u)^4 ≤ u^(1/200:ℝ) := by
    calc
      (102400:ℝ)*(logb 2 u)^4 = (102400:ℝ)/(log 2)^(4:ℕ) * (log u)^(4:ℕ) := by
        simp only [Real.logb,div_pow]; ring
      _ ≤ u^(1/200:ℝ) := by simpa only [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast] using hh
  have hm := mul_le_mul_of_nonneg_left hden (rpow_nonneg hu0.le (199/200:ℝ))
  have he : u^(199/200:ℝ)*u^(1/200:ℝ) = u := by
    rw [← Real.rpow_add hu0]; norm_num
  rw [he] at hm
  refine ⟨hu,?_⟩
  have hid : ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 = u/(102400*(logb 2 u)^4) := by
    field_simp
    ; ring
  rw [hid]
  exact (le_div_iff₀ (by positivity : (0:ℝ) < 102400*(logb 2 u)^4)).mpr (by nlinarith)

lemma longCycle_scale_ready : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    4 ≤ D ∧ 4 ≤ D^(51/50:ℝ) ∧
    ∀ u : ℝ, D^(51/50:ℝ) < u →
      0 < (1/32:ℝ)/(logb 2 u)^2 ∧ (1/32:ℝ)/(logb 2 u)^2 ≤ 1 ∧
      1 ≤ ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 ∧
      D^(101/100:ℝ) < ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp longCycle_power_margin
  refine ⟨max 4 Q,?_⟩
  intro D hD
  have hD4 : 4 ≤ D := (le_max_left _ _).trans hD
  have hD1 : 1 ≤ D := by linarith
  have hDp : 0 < D := by linarith
  have hTD : D ≤ D^(51/50:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD1
      (by norm_num : (1:ℝ) ≤ 51/50)
  refine ⟨hD4,hD4.trans hTD,?_⟩
  intro u hu
  have huQ : Q ≤ u := (le_max_right 4 Q).trans (hD.trans (hTD.trans hu.le))
  obtain ⟨hu4,hq⟩ := hQ u huQ
  have hlog : 1 ≤ logb 2 u := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=u)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at h
    exact h
  have hd : 0 < (logb 2 u)^2 := by positivity
  have hα : 0 < (1/32:ℝ)/(logb 2 u)^2 := by positivity
  have hα1 : (1/32:ℝ)/(logb 2 u)^2 ≤ 1 := by
    apply (div_le_one hd).mpr
    nlinarith [sq_nonneg (logb 2 u-1)]
  have hmargin : D^(101/100:ℝ) < u^(199/200:ℝ) := by
    have hstrict := Real.rpow_lt_rpow (Real.rpow_nonneg hDp.le (51/50:ℝ)) hu
      (by norm_num : (0:ℝ) < 199/200)
    rw [← Real.rpow_mul hDp.le] at hstrict
    have hle := Real.rpow_le_rpow_of_exponent_le hD1
      (by norm_num : (101/100:ℝ) ≤ (51/50)*(199/200))
    exact hle.trans_lt hstrict
  have hpow1 : 1 ≤ D^(101/100:ℝ) := Real.one_le_rpow hD1 (by norm_num)
  exact ⟨hα,hα1,hpow1.trans (hmargin.le.trans hq),hmargin.trans_le hq⟩

lemma external_induce_image (G : SimpleGraph V) (A : Finset V) (hG : SupportedOn G A)
    (U : Finset {x // x ∈ A}) :
    externalOn G (U.image Subtype.val) =
      (externalOn (G.induce (A : Set V)) U).image Subtype.val := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨_,hyU,x,hx,hxy⟩ := Finset.mem_filter.mp hy
    have hyA := (hG hxy).2
    obtain ⟨x',hx',heq⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨⟨y,hyA⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,rfl⟩
    · intro hy'
      exact hyU (Finset.mem_image.mpr ⟨⟨y,hyA⟩,hy',rfl⟩)
    · exact ⟨x',hx',by simpa only [SimpleGraph.induce_adj,heq] using hxy⟩
  · intro hy
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨_,hyU,x,hx,hxy⟩ := Finset.mem_filter.mp hy'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · intro hy
      obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hy
      have heq' : z = y' := Subtype.ext heq
      exact hyU (heq' ▸ hz)
    · exact ⟨x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,hxy⟩

lemma sparse_neighborhood_from_cycle_exclusion (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) (ℓ : ℝ) (hNL : NoLongCycle G ℓ)
    (hα : 0 < (1/32:ℝ)/(logb 2 A.card)^2)
    (hα1 : (1/32:ℝ)/(logb 2 A.card)^2 ≤ 1)
    (hq : 1 ≤ ((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100)
    (hmargin : ℓ < ((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100) :
    ∃ U ⊆ A, U.Nonempty ∧ 2*U.card ≤ A.card ∧
      ((externalOn G U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 A.card)^2 := by
  classical
  by_contra hno
  let H := G.induce (A : Set V)
  let α := (1/32:ℝ)/(logb 2 A.card)^2
  have hexp : VertexExpansion H α := by
    intro U hU hhalf
    let W := U.image Subtype.val
    have hW : W ⊆ A := by
      intro x hx
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      exact x'.property
    have hcard : W.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hWne : W.Nonempty := hU.image _
    have hWhalf : 2*W.card ≤ A.card := by simpa [hcard] using hhalf
    have hs : ¬ ((externalOn G W).card : ℝ) < (1/32:ℝ)*W.card/(logb 2 A.card)^2 :=
      fun hs => hno ⟨W,hW,hWne,hWhalf,hs⟩
    have hbound := le_of_not_gt hs
    have heq := external_induce_image G A hG U
    have hcardext := congrArg Finset.card heq
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcardext
    have hext : externalNeighbors H U = externalOn H U := by rfl
    rw [hext]
    change α*(U.card:ℝ) ≤ (externalOn H U).card
    rw [← hcardext]
    dsimp [α]
    rw [← hcard]
    calc
      (1/32:ℝ)/(logb 2 A.card)^2 * (W.card:ℝ) = (1/32:ℝ)*(W.card:ℝ)/(logb 2 A.card)^2 := by ring
      _ ≤ ((externalOn G W).card:ℝ) := hbound
  have hq' : 1 ≤ α^2*(Fintype.card {x // x ∈ A})/100 := by simpa [α] using hq
  obtain ⟨a,p,hp,hplen⟩ := long_cycle_of_vertex_expansion H α hα hα1 hexp hq'
  let f : H →g G := ⟨Subtype.val,fun h => h⟩
  have hc := hp.map (f:=f) (by exact Subtype.val_injective)
  have hlen := hNL a.val (p.map f) hc
  simp only [SimpleGraph.Walk.length_map] at hlen
  have hplen' : α^2*(A.card:ℝ)/100 < (p.length:ℝ) := by simpa using hplen
  dsimp [α] at hplen'
  linarith

lemma splitPotential_scale_bound (D x : ℝ) (hD : 4 ≤ D) :
    splitPotential (D^(51/50:ℝ)) x ≤ 1+2/logb 2 D := by
  have hD1 : 1 ≤ D := by linarith
  have hDp : 0 < D := by linarith
  have hLD : 2 ≤ logb 2 D := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=4) (y:=D)
      (by norm_num) (by norm_num) hD
    have h4 : logb 2 (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2^(2:ℕ) by norm_num,Real.logb_pow]
      norm_num
    rw [h4] at h
    exact h
  have hLD0 : 0 < logb 2 D := by linarith
  have hlogT : logb 2 (D^(51/50:ℝ)/2) = (51/50:ℝ)*logb 2 D-1 := by
    rw [Real.logb_div (Real.rpow_pos_of_pos hDp _).ne' (by norm_num),
      Real.logb_rpow_eq_mul_logb_of_pos hDp]
    norm_num
  have hT0 : 0 < logb 2 (D^(51/50:ℝ)/2) := by rw [hlogT]; linarith
  have hrecip : 1/logb 2 (D^(51/50:ℝ)/2) ≤ 2/logb 2 D := by
    apply (div_le_div_iff₀ hT0 hLD0).mpr
    rw [hlogT]
    linarith
  have hbasepos : 0 < D^(51/50:ℝ)/2 := by positivity
  have hmaxlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) hbasepos
    (le_max_right x (D^(51/50:ℝ)/2))
  have hmax0 : 0 < logb 2 (max x (D^(51/50:ℝ)/2)) := lt_of_lt_of_le hT0 hmaxlog
  have hinv := one_div_pos.mpr hmax0
  dsimp [splitPotential]
  linarith

lemma partition_replace_head {G H : SimpleGraph V} {C L : List (SimpleGraph V)}
    (hG : GraphPartition G (H::C)) (hH : GraphPartition H L) :
    GraphPartition G (C++L) := by
  intro x y
  have h := hG x y
  simp only [edgeOccurrences_cons] at h
  rw [edgeOccurrences_append,hH x y]
  omega

theorem scale_boxes : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      2*(edgeCount G : ℝ)/A.card ≤ D →
    ∃ (C : List (SimpleGraph V)) (L : List (AssignedPiece V)),
      (∀ K ∈ C, IsCycleGraph K ∧ D^(101/100:ℝ) ≤ (edgeCount K : ℝ)) ∧
      (C.length : ℝ) ≤ A.card/(2*D^(1/100:ℝ)) ∧
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧ (P.vertices.card : ℝ) ≤ D^(51/50:ℝ)) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      GraphPartition G (C++L.map AssignedPiece.graph) ∧
      (L.map (fun P => (P.vertices.card : ℝ))).sum ≤ (1+2/logb 2 D)*A.card := by
  classical
  obtain ⟨Dsp,hsp⟩ := longCycle_scale_ready
  refine ⟨Dsp,?_⟩
  intro D hD V _ _ G A hA hG hdeg
  obtain ⟨hD4,hT4,hnum⟩ := hsp D hD
  have hDp : 0 < D := by linarith
  have hA0 : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  obtain ⟨H,C,hHG,hNL,hC,hpartC,hbudget⟩ := remove_long_cycles G (D^(101/100:ℝ))
  have hHA : SupportedOn H A := fun _ _ h => hG (hHG h)
  have hsplit : ∀ B ⊆ A, ∀ K : SimpleGraph V, K ≤ H → SupportedOn K B → D^(51/50:ℝ) < (B.card:ℝ) →
      ∃ U ⊆ B, U.Nonempty ∧ 2*U.card ≤ B.card ∧
        ((externalOn K U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 B.card)^2 := by
    intro B hB K hK hs hlarge
    obtain ⟨ha,ha1,hq,hm⟩ := hnum B.card hlarge
    exact sparse_neighborhood_from_cycle_exclusion K B hs _ (hNL.mono hK) ha ha1 hq hm
  obtain ⟨L,hL,hcov,hpartL,hcost⟩ := box_recursion H A (D^(51/50:ℝ)) hT4 hA hHA hsplit
  refine ⟨C,L,hC,?_,hL,hcov,partition_replace_head hpartC hpartL,?_⟩
  · have hdeg' := (div_le_iff₀ hA0).mp hdeg
    have he : D^(101/100:ℝ) = D*D^(1/100:ℝ) := by
      rw [show (101/100:ℝ) = 1+1/100 by norm_num,Real.rpow_add hDp,Real.rpow_one]
    rw [he] at hbudget
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*D^(1/100:ℝ))).mpr
    have hnonneg : (0:ℝ) ≤ edgeCount H := Nat.cast_nonneg _
    nlinarith
  · have hfbound := splitPotential_scale_bound D A.card hD4
    have hplain : (L.map (fun P => (P.vertices.card:ℝ))).sum ≤
        (L.map (fun P => (P.vertices.card:ℝ)*splitPotential (D^(51/50:ℝ)) P.vertices.card)).sum := by
      apply List.sum_le_sum
      intro P hP
      have hb := (splitPotential_bounds (D^(51/50:ℝ)) P.vertices.card hT4).1
      have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg P.vertices.card)
      simpa using hm
    have hmul := mul_le_mul_of_nonneg_left hfbound hA0.le
    nlinarith

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open Finset SimpleGraph Classical Real
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

lemma edgeCount_sup_le (G H : SimpleGraph V) : edgeCount (G ⊔ H) ≤ edgeCount G + edgeCount H := by
  classical
  simpa [edgeCount, SimpleGraph.edgeFinset_sup] using Finset.card_union_le G.edgeFinset H.edgeFinset

lemma crossing_count (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B) :
    edgeCount (crossingGraph G A B) = cutCount G A B := by
  classical
  have hinj : Set.InjOn (fun e : V × V => s(e.1,e.2)) (G.interedges A B : Set (V×V)) := by
    intro e he f hf hh
    rcases Sym2.mk_eq_mk_iff.mp hh with hh | hh
    · exact hh
    · have heA := (G.mem_interedges_iff.mp he).1
      have hfB := (G.mem_interedges_iff.mp hf).2.1
      have heq : e.1 = f.2 := congrArg Prod.fst hh
      exact False.elim (Finset.disjoint_left.mp hd heA (heq.symm ▸ hfB))
  have heq : (crossingGraph G A B).edgeFinset =
      (G.interedges A B).image (fun e : V×V => s(e.1,e.2)) := by
    ext e
    induction e using Sym2.inductionOn with | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨hxy,(⟨hx,hy⟩|⟨hx,hy⟩)⟩
        · exact Finset.mem_image.mpr ⟨(x,y),G.mem_interedges_iff.mpr ⟨hx,hy,hxy⟩,rfl⟩
        · exact Finset.mem_image.mpr ⟨(y,x),G.mem_interedges_iff.mpr ⟨hy,hx,hxy.symm⟩,
            Sym2.eq_swap⟩
      · rintro h
        obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp h
        obtain ⟨ha,hb,hg⟩ := G.mem_interedges_iff.mp hab
        rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (x,y))).mp he with he | he
        · cases he; exact ⟨hg,Or.inl ⟨ha,hb⟩⟩
        · cases he; exact ⟨hg.symm,Or.inr ⟨hb,ha⟩⟩
  simp only [edgeCount,heq,Finset.card_image_of_injOn hinj,cutCount]

lemma log2_split_budget {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    min a b + a*a.log2 + b*b.log2 ≤ (a+b)*(a+b).log2 := by
  have hm : Monotone Nat.log2 := by
    intro m n h
    simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) h)
  have hla := hm (show a ≤ a+b by omega)
  have hlb := hm (show b ≤ a+b by omega)
  rcases le_total a b with hab | hba
  · have hhalf := hm (show 2*a ≤ a+b by omega)
    rw [Nat.log2_two_mul (by omega)] at hhalf
    rw [min_eq_left hab]
    nlinarith
  · have hhalf := hm (show 2*b ≤ a+b by omega)
    rw [Nat.log2_two_mul (by omega)] at hhalf
    rw [min_eq_right hba]
    nlinarith

lemma partition_combine {G K G₁ G₂ H₁ H₂ : SimpleGraph V}
    {L₁ L₂ : List (SimpleGraph V)}
    (hp₁ : GraphPartition G₁ (H₁::L₁)) (hp₂ : GraphPartition G₂ (H₂::L₂))
    (hcover : ∀ x y, G.Adj x y ↔ K.Adj x y ∨ G₁.Adj x y ∨ G₂.Adj x y)
    (hd₁ : Disjoint K G₁) (hd₂ : Disjoint K G₂) (hd₃ : Disjoint G₁ G₂) :
    GraphPartition G ((K ⊔ H₁ ⊔ H₂)::(L₁++L₂)) := by
  classical
  have hle₁ : H₁ ≤ G₁ := partition_member_le hp₁ (by simp)
  have hle₂ : H₂ ≤ G₂ := partition_member_le hp₂ (by simp)
  intro x y
  have h₁ := hp₁ x y
  have h₂ := hp₂ x y
  have hd₁ := SimpleGraph.disjoint_left.mp hd₁ x y
  have hd₂ := SimpleGraph.disjoint_left.mp hd₂ x y
  have hd₃ := SimpleGraph.disjoint_left.mp hd₃ x y
  have hh₁ := @hle₁ x y
  have hh₂ := @hle₂ x y
  have hc := hcover x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append,SimpleGraph.sup_adj] at *
  by_cases hK : K.Adj x y <;> by_cases hG₁ : G₁.Adj x y <;>
    by_cases hG₂ : G₂.Adj x y <;> by_cases hH₁ : H₁.Adj x y <;>
    by_cases hH₂ : H₂.Adj x y <;> simp_all

lemma cut_split_properties {V : Type cycleUniverse5} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A U : Finset V)
    (hG : SupportedOn G A) (_hU : U ⊆ A) :
    (∀ x y, G.Adj x y ↔ (crossingGraph G U (A\U)).Adj x y ∨
        (restrictGraph G U).Adj x y ∨ (restrictGraph G (A\U)).Adj x y) ∧
    Disjoint (crossingGraph G U (A\U)) (restrictGraph G U) ∧
    Disjoint (crossingGraph G U (A\U)) (restrictGraph G (A\U)) ∧
    Disjoint (restrictGraph G U) (restrictGraph G (A\U)) := by
  constructor
  · intro x y
    change G.Adj x y ↔ (G.Adj x y ∧ _) ∨ (G.Adj x y ∧ _) ∨ (G.Adj x y ∧ _)
    have hs := @hG x y
    simp only [Finset.mem_sdiff]
    tauto
  · simp only [SimpleGraph.disjoint_left, crossingGraph, restrictGraph,Finset.mem_sdiff]
    tauto

lemma empty_supported_graph {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {A : Finset V}
    (hG : SupportedOn G A) (hA : A.card ≤ 1) : G = ⊥ := by
  ext x y
  constructor
  · intro h
    obtain ⟨hx,hy⟩ := hG h
    have hxy := Finset.card_le_one.mp hA x hx y hy
    exact False.elim (G.ne_of_adj h hxy)
  · simp

theorem cut_extraction (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ 2 ≤ P.vertices.card ∧
        CutExpansionOn P.graph P.vertices σ) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧
      SupportedOn H A ∧
      (edgeCount H : ℝ) ≤ σ * A.card * A.card.log2 := by
  classical
  induction hcard : A.card using Nat.strong_induction_on generalizing A G with
  | h n ih =>
    by_cases hsmall : A.card ≤ 1
    · have he := empty_supported_graph hG hsmall
      refine ⟨[],⊥,by simp,by simp,?_,?_,?_⟩
      · subst G
        intro x y
        simp
      · intro x y h; exact False.elim h
      · simp only [edgeCount_bot,Nat.cast_zero]
        positivity
    by_cases hexp : CutExpansionOn G A σ
    · refine ⟨[⟨A,G,hG⟩],⊥,?_,by simp,?_,?_,?_⟩
      · intro P hP
        have he := List.mem_singleton.mp hP
        subst P
        exact ⟨fun _ h => h,by change 2 ≤ A.card; omega,hexp⟩
      · intro x y; simp
      · intro x y h; exact False.elim h
      · simp only [edgeCount_bot,Nat.cast_zero]
        positivity
    unfold CutExpansionOn at hexp
    push Not at hexp
    obtain ⟨U,hU,hcut⟩ := hexp
    have hdisUB : Disjoint U (A\U) := Finset.disjoint_left.mpr
      (fun _ hu hb => (Finset.mem_sdiff.mp hb).2 hu)
    have hcnt : (0 : ℝ) ≤ cutCount G U (A\U) := Nat.cast_nonneg _
    have hσpos : 0 < σ := by
      by_contra h
      have : σ = 0 := le_antisymm (le_of_not_gt h) hσ
      rw [this,zero_mul] at hcut
      linarith
    have hUpos : 0 < U.card := by
      by_contra h
      have hz : U.card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_left (0:ℝ) ((A\U).card:ℝ)]
    have hBpos : 0 < (A\U).card := by
      by_contra h
      have hz : (A\U).card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_right (U.card:ℝ) (0:ℝ)]
    have hcardSum := Finset.card_sdiff_add_card_eq_card hU
    have hUlt : U.card < n := by omega
    have hBlt : (A\U).card < n := by omega
    obtain ⟨R₁,H₁,hR₁,hd₁,hp₁,hs₁,hc₁⟩ := ih U.card hUlt (restrictGraph G U) U
      (restrictGraph_supported G U) rfl
    obtain ⟨R₂,H₂,hR₂,hd₂,hp₂,hs₂,hc₂⟩ := ih (A\U).card hBlt (restrictGraph G (A\U)) (A\U)
      (restrictGraph_supported G (A\U)) rfl
    let K := crossingGraph G U (A\U)
    obtain ⟨hcover,hdis₁,hdis₂,hdis₃⟩ := cut_split_properties G A U hG hU
    refine ⟨R₁++R₂,K ⊔ H₁ ⊔ H₂,?_,?_,?_,?_,?_⟩
    · intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · obtain ⟨hPA,hPc,hPe⟩ := hR₁ P hP
        exact ⟨hPA.trans hU,hPc,hPe⟩
      · obtain ⟨hPA,hPc,hPe⟩ := hR₂ P hP
        exact ⟨hPA.trans Finset.sdiff_subset,hPc,hPe⟩
    · apply List.pairwise_append.mpr
      refine ⟨hd₁,hd₂,?_⟩
      intro P hP Q hQ
      exact hdisUB.mono
        (hR₁ P hP).1 (hR₂ Q hQ).1
    · simpa only [List.map_append] using partition_combine hp₁ hp₂ hcover hdis₁ hdis₂ hdis₃
    · intro x y h
      rcases h with (h|h)|h
      · exact hG h.1
      · exact ⟨hU (hs₁ h).1,hU (hs₁ h).2⟩
      · exact ⟨(Finset.mem_sdiff.mp (hs₂ h).1).1,(Finset.mem_sdiff.mp (hs₂ h).2).1⟩
    · have hcardK : edgeCount K = cutCount G U (A\U) :=
        crossing_count G U (A\U) hdisUB
      have hcost : (edgeCount (K⊔H₁⊔H₂) : ℝ) ≤
          edgeCount K + edgeCount H₁ + edgeCount H₂ := by
        exact_mod_cast (edgeCount_sup_le (K⊔H₁) H₂).trans
          (Nat.add_le_add_right (edgeCount_sup_le K H₁) _)
      have hpot := log2_split_budget hUpos hBpos
      have hpotR : min (U.card:ℝ) ((A\U).card:ℝ) + U.card*U.card.log2 +
          (A\U).card*(A\U).card.log2 ≤ (A.card:ℝ) * A.card.log2 := by
        have he : U.card+(A\U).card = A.card := by omega
        rw [he] at hpot
        exact_mod_cast hpot
      have hpay := mul_le_mul_of_nonneg_left hpotR hσ
      rw [hcardK] at hcost
      rw [← hcard]
      nlinarith

lemma cast_log2_le_logb {n : ℕ} (hn : 0 < n) : (n.log2 : ℝ) ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (by exact_mod_cast hn)).mpr
  rw [Real.rpow_natCast, Nat.log2_eq_log_two]
  exact_mod_cast Nat.pow_log_le_self 2 hn.ne'

lemma expansion_order_lower {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {A : Finset V} {σ : ℝ}
    (hA : 2 ≤ A.card) (he : CutExpansionOn G A σ) : σ+1 ≤ A.card := by
  classical
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hsub : {x} ⊆ A := Finset.singleton_subset_iff.mpr hx
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  simp only [Finset.card_singleton] at hcard
  have hB : (1:ℝ) ≤ (A\{x}).card := by exact_mod_cast (show 1 ≤ (A\{x}).card by omega)
  have hc := he {x} hsub
  simp only [Finset.card_singleton,Nat.cast_one,min_eq_left hB,mul_one] at hc
  have hbound : cutCount G {x} (A\{x}) ≤ (A\{x}).card := by
    simpa only [cutCount,Finset.card_singleton,one_mul] using G.card_interedges_le_mul {x} (A\{x})
  have hboundR : (cutCount G {x} (A\{x}) : ℝ) ≤ (A\{x}).card := by exact_mod_cast hbound
  have heqR : ((A\{x}).card:ℝ)+1 = A.card := by exact_mod_cast hcard
  linarith

open Filter Asymptotics Real in
lemma cut_scale_ready : ∀ᶠ D : ℝ in atTop,
    1 ≤ D ∧ 2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ)) ≤ D^(19/20:ℝ) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have he := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/20)).const_mul_left
    ((51/25:ℝ)/log 2)).eventuallyLE
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with D hD h
  have hDp : 0 < D := by linarith
  have hn : 0 ≤ (51/25:ℝ)/log 2 * log D := mul_nonneg (by positivity) (Real.log_nonneg hD)
  have hh : (51/25:ℝ)/log 2 * log D ≤ D^(1/20:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (Real.rpow_nonneg hDp.le _)] using h
  refine ⟨hD,?_⟩
  calc
    2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ)) = D^(9/10:ℝ)*((51/25:ℝ)/log 2*log D) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hDp]
      simp only [Real.logb]
      ring
    _ ≤ D^(9/10:ℝ)*D^(1/20:ℝ) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = D^(19/20:ℝ) := by rw [← Real.rpow_add hDp]; norm_num

theorem scale_cut_extraction : ∃ Dcut : ℝ, ∀ D ≥ Dcut,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      (A.card : ℝ) ≤ D^(51/50:ℝ) →
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ D^(9/10:ℝ) ≤ P.vertices.card ∧
        (P.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧ CutExpansionOn P.graph P.vertices (D^(9/10:ℝ))) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧ SupportedOn H A ∧
      2*(edgeCount H : ℝ)/A.card ≤ D^(19/20:ℝ) := by
  classical
  obtain ⟨Dcut,hready⟩ := Filter.eventually_atTop.mp cut_scale_ready
  refine ⟨Dcut,?_⟩
  intro D hD V _ _ G A hA hG hhi
  obtain ⟨hD₁,hscale⟩ := hready D hD
  have hDp : 0 < D := by linarith
  have hAp : 0 < A.card := Finset.card_pos.mpr hA
  have hAr : (0:ℝ) < A.card := by exact_mod_cast hAp
  obtain ⟨R,H,hR,hd,hp,hs,hcost⟩ := cut_extraction G A hG (D^(9/10:ℝ)) (by positivity)
  refine ⟨R,H,?_,hd,hp,hs,?_⟩
  · intro P hP
    obtain ⟨hsub,hsize,hexp⟩ := hR P hP
    have hlo := expansion_order_lower hsize hexp
    have hle : (P.vertices.card:ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hsub
    exact ⟨hsub,by linarith,hle.trans hhi,hexp⟩
  · have hlog := (cast_log2_le_logb hAp).trans
      (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hAr hhi)
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ D^(9/10:ℝ)*(A.card:ℝ) by positivity)
    have hscaleA := mul_le_mul_of_nonneg_right hscale hAr.le
    apply (div_le_iff₀ hAr).mpr
    nlinarith

end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ScaleHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph Classical Real
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

lemma edgeOccurrences_refine {I : Type cycleUniverse2} (L : List I)
    (g : I → SimpleGraph V) (f : I → List (SimpleGraph V))
    (h : ∀ i ∈ L, GraphPartition (g i) (f i)) (x y : V) :
    edgeOccurrences (L.flatMap f) x y = edgeOccurrences (L.map g) x y := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.flatMap_cons, edgeOccurrences_append, List.map_cons,
      edgeOccurrences_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

lemma graphPartition_refine {I : Type cycleUniverse3} {G : SimpleGraph V}
    {C : List (SimpleGraph V)} {L : List I}
    {g : I → SimpleGraph V} {f : I → List (SimpleGraph V)}
    (hp : GraphPartition G (C ++ L.map g))
    (h : ∀ i ∈ L, GraphPartition (g i) (f i)) :
    GraphPartition G (C ++ L.flatMap f) := by
  intro x y
  simpa only [edgeOccurrences_append, edgeOccurrences_refine L g f h] using hp x y

theorem scale_split : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      2*(edgeCount G : ℝ)/A.card ≤ D →
    ∃ (C : List (SimpleGraph V)) (L : List (AssignedPiece V))
      (R : AssignedPiece V → List (AssignedPiece V))
      (H : AssignedPiece V → SimpleGraph V),
      (∀ K ∈ C, IsCycleGraph K ∧ D^(101/100:ℝ) ≤ (edgeCount K : ℝ)) ∧
      (C.length : ℝ) ≤ A.card/(2*D^(1/100:ℝ)) ∧
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧
        (P.vertices.card : ℝ) ≤ D^(51/50:ℝ)) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      (L.map (fun P => (P.vertices.card : ℝ))).sum ≤ (1+2/logb 2 D)*A.card ∧
      (∀ P ∈ L,
        (∀ Q ∈ R P, Q.vertices ⊆ P.vertices ∧
          D^(9/10:ℝ) ≤ Q.vertices.card ∧
          (Q.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
          CutExpansionOn Q.graph Q.vertices (D^(9/10:ℝ))) ∧
        (R P).Pairwise (fun Q T => Disjoint Q.vertices T.vertices) ∧
        GraphPartition P.graph (H P :: (R P).map AssignedPiece.graph) ∧
        SupportedOn (H P) P.vertices ∧
        2*(edgeCount (H P) : ℝ)/P.vertices.card ≤ D^(19/20:ℝ)) ∧
      GraphPartition G (C ++ L.flatMap (fun P => H P :: (R P).map AssignedPiece.graph)) := by
  classical
  obtain ⟨D₁,h₁⟩ := scale_boxes.{u}
  obtain ⟨D₂,h₂⟩ := scale_cut_extraction.{u}
  refine ⟨max D₁ D₂, ?_⟩
  intro D hD V _ _ G A hA hs hd
  obtain ⟨C,L,hC,hCN,hL,hcover,hp,hcost⟩ :=
    h₁ D ((le_max_left _ _).trans hD) V G A hA hs hd
  have hres : ∀ P : AssignedPiece V,
      ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V), P ∈ L →
        (∀ Q ∈ R, Q.vertices ⊆ P.vertices ∧
          D^(9/10:ℝ) ≤ Q.vertices.card ∧
          (Q.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
          CutExpansionOn Q.graph Q.vertices (D^(9/10:ℝ))) ∧
        R.Pairwise (fun Q T => Disjoint Q.vertices T.vertices) ∧
        GraphPartition P.graph (H :: R.map AssignedPiece.graph) ∧
        SupportedOn H P.vertices ∧
        2*(edgeCount H : ℝ)/P.vertices.card ≤ D^(19/20:ℝ) := by
    intro P
    by_cases hP : P ∈ L
    · obtain ⟨R,H,hgood⟩ := h₂ D ((le_max_right _ _).trans hD) V
        P.graph P.vertices (hL P hP).2.1 P.supported (hL P hP).2.2
      exact ⟨R,H,fun _ => hgood⟩
    · exact ⟨[],⊥,fun hp => False.elim (hP hp)⟩
  choose R H hR using hres
  refine ⟨C,L,R,H,hC,hCN,hL,hcover,hcost,hR,?_⟩
  exact graphPartition_refine hp (fun P hP => (hR P hP).2.2.1)

end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Real Filter Finset
open scoped Topology

lemma scaleTheta_pos : 0 < scaleTheta := by norm_num [scaleTheta]
lemma scaleTheta_lt_one : scaleTheta < 1 := by norm_num [scaleTheta]

lemma inductionScale_zero (n : ℝ) : inductionScale n 0 = n := by
  simp [inductionScale]

lemma inductionScale_pos (n : ℝ) (hn : 0 < n) (j : ℕ) :
    0 < inductionScale n j := Real.rpow_pos_of_pos hn _

lemma inductionScale_succ (n : ℝ) (hn : 0 ≤ n) (j : ℕ) :
    inductionScale n (j+1) = (inductionScale n j) ^ scaleTheta := by
  simp only [inductionScale, pow_succ, Real.rpow_mul hn]

lemma inductionScale_gt_one (n : ℝ) (hn : 1 < n) (j : ℕ) :
    1 < inductionScale n j := by
  simpa [inductionScale] using Real.rpow_lt_rpow_of_exponent_lt hn
    (pow_pos scaleTheta_pos j)

lemma inductionScale_le (n : ℝ) (hn : 1 ≤ n) (j : ℕ) :
    inductionScale n j ≤ n := by
  have hp : scaleTheta ^ j ≤ 1 := pow_le_one₀ scaleTheta_pos.le scaleTheta_lt_one.le
  simpa [inductionScale] using Real.rpow_le_rpow_of_exponent_le hn hp

lemma inductionScale_log (n : ℝ) (hn : 0 < n) (j : ℕ) :
    logb 2 (inductionScale n j) = scaleTheta ^ j * logb 2 n := by
  exact Real.logb_rpow_eq_mul_logb_of_pos hn

lemma inductionScale_log_pos (n : ℝ) (hn : 1 < n) (j : ℕ) :
    0 < logb 2 (inductionScale n j) := by
  exact Real.logb_pos (by norm_num) (inductionScale_gt_one n hn j)

lemma inductionScale_log_succ (n : ℝ) (hn : 0 < n) (j : ℕ) :
    logb 2 (inductionScale n (j+1)) = scaleTheta * logb 2 (inductionScale n j) := by
  rw [inductionScale_log n hn, inductionScale_log n hn, pow_succ]
  ring

lemma inductionScale_add (n : ℝ) (hn : 0 ≤ n) (i K : ℕ) :
    inductionScale n (i+K) = (inductionScale n i) ^ (scaleTheta ^ K) := by
  simp only [inductionScale, pow_add, Real.rpow_mul hn]

lemma inductionScale_window : (51/50 : ℝ) * scaleTheta ^ 200 < 1/1000 ∧
    scaleTheta ^ 201 < 1/1000 := by
  norm_num [scaleTheta]

lemma inductionScale_tendsto (n : ℝ) (hn : 0 < n) :
    Tendsto (inductionScale n) atTop (𝓝 1) := by
  have ht := (Real.continuous_const_rpow (ne_of_gt hn)).tendsto 0
  change Tendsto (fun j : ℕ => n ^ (scaleTheta ^ j)) atTop (𝓝 1)
  simpa only [Function.comp_def, Real.rpow_zero] using
    ht.comp (tendsto_pow_atTop_nhds_zero_of_lt_one scaleTheta_pos.le scaleTheta_lt_one)

theorem inductionScale_first_cutoff (n Dstar : ℝ) (hD : 1 < Dstar) (hn : Dstar ≤ n) :
    ∃ m : ℕ, 0 < m ∧ inductionScale n m < Dstar ∧
      ∀ j < m, Dstar ≤ inductionScale n j := by
  have hn0 : 0 < n := lt_trans (by norm_num) (hD.trans_le hn)
  have he : ∀ᶠ j in atTop, inductionScale n j < Dstar :=
    (inductionScale_tendsto n hn0).eventually (gt_mem_nhds hD)
  have hex : ∃ j, inductionScale n j < Dstar := he.exists
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hm
    have hz : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hz, inductionScale_zero] at this
    linarith
  · intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)

theorem scale_reciprocal_log_sum (n : ℝ) (hn : 1 < n) (j : ℕ) :
    (∑ l ∈ Finset.range (j+1), 1 / logb 2 (inductionScale n l)) ≤
      20 / logb 2 (inductionScale n j) := by
  induction j with
  | zero =>
    simp only [zero_add, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact div_le_div_of_nonneg_right (by norm_num) (inductionScale_log_pos n hn 0).le
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hb : (∑ x ∈ range (j + 1), 1 / logb 2 (inductionScale n x)) +
        1 / logb 2 (inductionScale n (j+1)) ≤
        20 / logb 2 (inductionScale n j) + 1 / logb 2 (inductionScale n (j+1)) := by
      linarith [ih]
    apply hb.trans_eq
    rw [inductionScale_log_succ n (by linarith)]
    have hz : logb 2 (inductionScale n j) ≠ 0 := ne_of_gt (inductionScale_log_pos n hn j)
    dsimp [scaleTheta]
    field_simp
    ; ring

lemma exp_le_one_add_twice {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    exp x ≤ 1+2*x := by
  apply (Real.exp_bound_div_one_sub_of_interval hx (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-x)).mpr
  nlinarith

theorem scale_overlap_product (n C₀ : ℝ) (hn : 1 < n) (hC : 0 ≤ C₀) (j : ℕ)
    (hcut : 40*C₀ ≤ logb 2 (inductionScale n j)) :
    (∏ l ∈ Finset.range (j+1), (1 + C₀ / logb 2 (inductionScale n l))) ≤
      1 + 40*C₀ / logb 2 (inductionScale n j) := by
  have hL := inductionScale_log_pos n hn j
  have hsum : (∑ l ∈ Finset.range (j+1), C₀ / logb 2 (inductionScale n l)) ≤
      20*C₀ / logb 2 (inductionScale n j) := by
    have hh := mul_le_mul_of_nonneg_left (scale_reciprocal_log_sum n hn j) hC
    calc
      _ ≤ C₀ * (20 / logb 2 (inductionScale n j)) := by
        simpa only [Finset.mul_sum, mul_one_div] using hh
      _ = _ := by ring
  calc
    _ ≤ ∏ l ∈ Finset.range (j+1), exp (C₀ / logb 2 (inductionScale n l)) := by
      apply Finset.prod_le_prod
      · intro l hl
        have := div_nonneg hC (inductionScale_log_pos n hn l).le
        linarith
      · intro l hl
        simpa [add_comm] using Real.add_one_le_exp (C₀ / logb 2 (inductionScale n l))
    _ = exp (∑ l ∈ Finset.range (j+1), C₀ / logb 2 (inductionScale n l)) :=
      (Real.exp_sum _ _).symm
    _ ≤ exp (20*C₀ / logb 2 (inductionScale n j)) := Real.exp_le_exp.mpr hsum
    _ ≤ 1 + 2*(20*C₀ / logb 2 (inductionScale n j)) := by
      apply exp_le_one_add_twice (div_nonneg (by positivity) hL.le)
      apply (div_le_iff₀ hL).mpr
      linarith
    _ = _ := by ring

theorem scale_prefix_cycle_cost (n : ℝ) (hn : 1 < n) (j : ℕ) (A : ℕ → ℝ)
    (hA : ∀ l ∈ Finset.range (j+1), A l ≤ 2*n)
    (hscale : ∀ l ∈ Finset.range (j+1),
      1 / (inductionScale n l) ^ (1/100 : ℝ) ≤ 1 / logb 2 (inductionScale n l)) :
    (∑ l ∈ Finset.range (j+1), A l / (2*(inductionScale n l) ^ (1/100 : ℝ))) ≤
      20*n / logb 2 (inductionScale n j) := by
  have hn0 : 0 < n := by linarith
  calc
    _ ≤ ∑ l ∈ Finset.range (j+1), n * (1 / logb 2 (inductionScale n l)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hp : 0 < (inductionScale n l) ^ (1/100 : ℝ) :=
        Real.rpow_pos_of_pos (inductionScale_pos n hn0 l) _
      calc
        _ ≤ 2*n / (2*(inductionScale n l) ^ (1/100 : ℝ)) :=
          div_le_div_of_nonneg_right (hA l hl) (by positivity)
        _ = n * (1 / (inductionScale n l) ^ (1/100 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hscale l hl) hn0.le
    _ = n * (∑ l ∈ Finset.range (j+1), 1 / logb 2 (inductionScale n l)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ n * (20 / logb 2 (inductionScale n j)) :=
      mul_le_mul_of_nonneg_left (scale_reciprocal_log_sum n hn j) hn0.le
    _ = _ := by ring

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

theorem scale_splitter : ∃ Dsp : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V],
    ∃ split : ∀ (_D : ℝ) (P : AssignedPiece V), StageSplit P,
      ∀ D ≥ Dsp, ∀ P, P.vertices.Nonempty →
        2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D → (split D P).Bounded D := by
  obtain ⟨Dsp,hsp⟩ := scale_split
  refine ⟨Dsp,?_⟩
  intro V _ _
  have hex (D : ℝ) (P : AssignedPiece V) : ∃ s : StageSplit P,
      Dsp ≤ D → P.vertices.Nonempty → 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D → s.Bounded D := by
    by_cases h : Dsp ≤ D ∧ P.vertices.Nonempty ∧ 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D
    · obtain ⟨C,L,R,H,hC,hCl,hL,hcover,horder,hR,hpart⟩ :=
        hsp D h.1 V P.graph P.vertices h.2.1 P.supported h.2.2
      have hpart' : GraphPartition P.graph (C ++ L.map AssignedPiece.graph) := by
        intro x y
        rw [edgeOccurrences_append, ← edgeOccurrences_refine L AssignedPiece.graph
          (fun B => H B :: (R B).map AssignedPiece.graph) (fun B hB => (hR B hB).2.2.1)]
        simpa only [edgeOccurrences_append] using hpart x y
      let s : StageSplit P := {
        cycles := C, boxes := L, pieces := R, remainder := H
        cycles_good := fun K hK => (hC K hK).1
        box_subset := fun B hB => (hL B hB).1
        box_nonempty := fun _ B hB => (hL B hB).2.1
        box_cover := hcover
        piece_subset := fun B hB Q hQ => (hR B hB).1 Q hQ |>.1
        piece_disjoint := fun B hB => (hR B hB).2.1
        remainder_supported := fun B hB => (hR B hB).2.2.2.1
        box_partition := fun B hB => (hR B hB).2.2.1
        partition := hpart' }
      refine ⟨s,fun _ _ _ => ⟨hCl,horder,fun B hB => (hL B hB).2.2,?_,?_⟩⟩
      · exact fun B hB Q hQ => (hR B hB).1 Q hQ |>.2
      · exact fun B hB => (hR B hB).2.2.2.2
    · exact ⟨StageSplit.trivial P,fun hD hP hdeg => False.elim (h ⟨hD,hP,hdeg⟩)⟩
  choose s hs using hex
  exact ⟨s,fun D hD P hP hdeg => hs D P hD hP hdeg⟩

lemma StageSplit.mem_children {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) (Q : AssignedPiece V) :
    Q ∈ s.children ↔ ∃ B ∈ s.boxes, Q.vertices = B.vertices ∧ Q.graph = s.remainder B := by
  simp only [StageSplit.children, List.mem_pmap]
  constructor
  · rintro ⟨B,hB,rfl⟩; exact ⟨B,hB,rfl,rfl⟩
  · rintro ⟨B,hB,hv,hg⟩
    refine ⟨B,hB,?_⟩
    cases Q; cases B; simp_all

lemma StageSplit.children_map {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P)
    {α : Type cycleUniverse4} (f : Finset V → SimpleGraph V → α) :
    s.children.map (fun Q => f Q.vertices Q.graph) =
      s.boxes.map (fun B => f B.vertices (s.remainder B)) := by
  unfold StageSplit.children
  rw [List.map_pmap]
  change List.pmap (fun B (_ : B ∈ s.boxes) => f B.vertices (s.remainder B)) s.boxes _ = _
  exact List.pmap_eq_map (fun B (h : B ∈ s.boxes) => h)

lemma list_disjoint_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (Finset V)) (A : Finset V)
    (hd : L.Pairwise Disjoint) (hA : ∀ B ∈ L, B ⊆ A) :
    (L.map Finset.card).sum ≤ A.card := by
  induction L generalizing A with
  | nil => simp
  | cons B L ih =>
    obtain ⟨hBL,hd⟩ := List.pairwise_cons.mp hd
    have hBA := hA B (by simp)
    have hLA : ∀ C ∈ L, C ⊆ A \ B := by
      intro C hC v hv
      exact Finset.mem_sdiff.mpr ⟨hA C (by simp [hC]) hv,
        fun hb => Finset.disjoint_left.mp (hBL C hC) hb hv⟩
    have hh := ih (A \ B) hd hLA
    have hc := Finset.card_sdiff_of_subset hBA
    have hBAcard := Finset.card_le_card hBA
    simp only [List.map_cons,List.sum_cons]
    omega

lemma vertexMass_nonneg {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) : 0 ≤ vertexMass L :=
  List.sum_nonneg (fun x hx => by obtain ⟨P,_,rfl⟩ := List.mem_map.mp hx; positivity)

lemma vertexMass_flatMap {I : Type cycleUniverse5} (L : List I) (f : I → List (AssignedPiece V)) :
    vertexMass (L.flatMap f) = (L.map (fun i => vertexMass (f i))).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [ih]

lemma StageSplit.children_mass {P : AssignedPiece V} (s : StageSplit P) :
    vertexMass s.children = vertexMass s.boxes := by
  unfold vertexMass
  rw [s.children_map (fun A _ => (A.card:ℝ))]

lemma StageSplit.pieces_mass {P : AssignedPiece V} (s : StageSplit P) {B : AssignedPiece V}
    (hB : B ∈ s.boxes) : vertexMass (s.pieces B) ≤ B.vertices.card := by
  have hh := list_disjoint_card_le ((s.pieces B).map AssignedPiece.vertices) B.vertices
    (List.pairwise_map.mpr (s.piece_disjoint B hB)) (by
      intro A hA; obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hA
      exact s.piece_subset B hB Q hQ)
  simpa [vertexMass,List.map_map,Function.comp_def] using (Nat.cast_le.mpr hh : (_:ℝ) ≤ _)

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma advance_add (s : SplitSystem V) (j k l) (L) :
    advance s j (k+l) L = advance s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp
  | succ l ih => simp only [Nat.add_succ,advance_succ,ih,Nat.add_assoc]

lemma advance_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse6}
    (L : List I) (f : I → List (AssignedPiece V)) :
    advance s j k (L.flatMap f) = L.flatMap (fun i => advance s j k (f i)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [advance_succ,nextLayer,ih,List.flatMap_assoc]

lemma nextLayer_mem (s : SplitSystem V) (j) (L) (Q : AssignedPiece V) :
    Q ∈ nextLayer s j L ↔ ∃ P ∈ L, ∃ B ∈ (s j P).boxes,
      Q.vertices = B.vertices ∧ Q.graph = (s j P).remainder B := by
  simp only [nextLayer,List.mem_flatMap,StageSplit.mem_children]

lemma advance_subset (s : SplitSystem V) (j k) (L) (A : Finset V)
    (hA : ∀ P ∈ L, P.vertices ⊆ A) :
    ∀ Q ∈ advance s j k L, Q.vertices ⊆ A := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,_⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    rw [hv]
    exact ((s (j+k) P).box_subset B hB).trans (ih P hP)

lemma advance_nonempty (s : SplitSystem V) (j k) (L)
    (hL : ∀ P ∈ L, P.vertices.Nonempty) :
    ∀ Q ∈ advance s j k L, Q.vertices.Nonempty := by
  induction k with
  | zero => exact hL
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,_⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    rw [hv]
    exact (s (j+k) P).box_nonempty (ih P hP) B hB

lemma advance_cover (s : SplitSystem V) (j k) (L) (P : AssignedPiece V) (hP : P ∈ L)
    (v : V) (hv : v ∈ P.vertices) : ∃ Q ∈ advance s j k L, v ∈ Q.vertices := by
  induction k with
  | zero => exact ⟨P,hP,hv⟩
  | succ k ih =>
    obtain ⟨Q,hQ,hvQ⟩ := ih
    obtain ⟨B,hB,hvB⟩ := (s (j+k) Q).box_cover v hvQ
    let T : AssignedPiece V := ⟨B.vertices,(s (j+k) Q).remainder B,
      (s (j+k) Q).remainder_supported B hB⟩
    exact ⟨T,(nextLayer_mem s (j+k) _ T).mpr ⟨Q,hQ,B,hB,rfl,rfl⟩,hvB⟩

lemma list_union_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) (v : V) :
    v ∈ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅ ↔ ∃ P ∈ L, v ∈ P.vertices := by
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]
    aesop

lemma list_union_card {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) :
    ((L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card:ℝ) ≤ vertexMass L := by
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.foldr_cons,vertexMass_cons]
    have hc := Finset.card_union_le P.vertices (L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅)
    have hc' : ((P.vertices ∪ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card:ℝ) ≤
        P.vertices.card + (L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card := by exact_mod_cast hc
    linarith

lemma list_cover_card_le (L : List (AssignedPiece V)) (A : Finset V)
    (hcover : ∀ v ∈ A, ∃ P ∈ L, v ∈ P.vertices) : (A.card:ℝ) ≤ vertexMass L := by
  have hsub : A ⊆ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅ :=
    fun v hv => (list_union_mem L v).mpr (hcover v hv)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (list_union_card L)

lemma advance_mass_lower (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (P.vertices.card:ℝ) ≤ vertexMass (advance s j k [P]) :=
  list_cover_card_le _ _ (fun v hv => advance_cover s j k [P] P (by simp) v hv)

lemma nextLayer_mass_bound (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (D : ℝ)
    (hb : ∀ P ∈ L, (s j P).Bounded D) :
    vertexMass (nextLayer s j L) ≤ (1+2/logb 2 D)*vertexMass L := by
  induction L with
  | nil => simp [nextLayer]
  | cons P L ih =>
    have hP := (hb P (by simp)).2.1
    have hL := ih (fun Q hQ => hb Q (by simp [hQ]))
    simp only [nextLayer,List.flatMap_cons,vertexMass_append,StageSplit.children_mass,
      vertexMass_cons] at hL ⊢
    change vertexMass (s j P).boxes ≤ _ at hP
    nlinarith

lemma advance_valid (s : SplitSystem V) (n Dstar : ℝ) (hn : 0 ≤ n)
    (hs : ∀ l P, Dstar ≤ inductionScale n l → P.vertices.Nonempty →
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n l →
      (s l P).Bounded (inductionScale n l))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hL : ∀ P ∈ L, P.vertices.Nonempty)
    (hdeg : ∀ P ∈ L, 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n j)
    (hcut : ∀ l, j ≤ l → l < j+k → Dstar ≤ inductionScale n l) :
    ∀ P ∈ advance s j k L,
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n (j+k) := by
  induction k with
  | zero => simpa using hdeg
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    have hPdeg := ih (fun l hlj hl => hcut l hlj (by omega)) P hP
    have hb := hs (j+k) P (hcut (j+k) (by omega) (by omega))
      (advance_nonempty s j k L hL P hP) hPdeg
    rw [hv,hg,show j+(k+1) = (j+k)+1 by omega,inductionScale_succ n hn]
    exact hb.2.2.2.2 B hB

lemma advance_bounded (s : SplitSystem V) (n Dstar : ℝ) (hn : 0 ≤ n)
    (hs : ∀ l P, Dstar ≤ inductionScale n l → P.vertices.Nonempty →
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n l →
      (s l P).Bounded (inductionScale n l))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hL : ∀ P ∈ L, P.vertices.Nonempty)
    (hdeg : ∀ P ∈ L, 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n j)
    (hcut : ∀ l, j ≤ l → l ≤ j+k → Dstar ≤ inductionScale n l) :
    ∀ P ∈ advance s j k L, (s (j+k) P).Bounded (inductionScale n (j+k)) := by
  intro P hP
  exact hs (j+k) P (hcut _ (by omega) (by omega)) (advance_nonempty s j k L hL P hP)
    (advance_valid s n Dstar hn hs j k L hL hdeg (fun l hlj hl => hcut l hlj (by omega)) P hP)

lemma advance_mass_global_product (s : SplitSystem V) (n : ℝ) (hn : 1 < n)
    (j k : ℕ) (L : List (AssignedPiece V))
    (hb : ∀ l < k, ∀ P ∈ advance s j l L, (s (j+l) P).Bounded (inductionScale n (j+l))) :
    vertexMass (advance s j k L) ≤ vertexMass L *
      ∏ l ∈ Finset.range (j+k), (1+2/logb 2 (inductionScale n l)) := by
  have hfac (l) : 1 ≤ 1+2/logb 2 (inductionScale n l) := by
    have := div_nonneg (by norm_num : (0:ℝ) ≤ 2) (inductionScale_log_pos n hn l).le
    linarith
  induction k with
  | zero =>
    simp only [advance_zero,Nat.add_zero]
    exact le_mul_of_one_le_right (vertexMass_nonneg L) (Finset.one_le_prod (fun l _ => hfac l))
  | succ k ih =>
    have hm := nextLayer_mass_bound s (j+k) (advance s j k L) (inductionScale n (j+k))
      (hb k (by omega))
    have hi := mul_le_mul_of_nonneg_left (ih (fun l hl => hb l (by omega))) ((hfac (j+k)).trans' (by norm_num : (0:ℝ) ≤ 1))
    rw [advance_succ,show j+(k+1) = (j+k)+1 by omega,Finset.prod_range_succ]
    calc
      _ ≤ (1+2/logb 2 (inductionScale n (j+k))) * vertexMass (advance s j k L) := hm
      _ ≤ _ := by nlinarith only [hi]

end
end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ScaleDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma graphUnion_adj {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (SimpleGraph V)) (x y : V) :
    (graphUnion L).Adj x y ↔ ∃ G ∈ L, G.Adj x y := by
  induction L with
  | nil => simp
  | cons G L ih => simp only [graphUnion_cons,SimpleGraph.sup_adj,ih,List.mem_cons]; aesop

lemma edgeOccurrences_pos (L : List (SimpleGraph V)) (x y : V) :
    0 < edgeOccurrences L x y ↔ (graphUnion L).Adj x y := by
  simp [edgeOccurrences,List.countP_pos_iff,graphUnion_adj]

lemma graphPartition_union {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : graphUnion L = G := by
  ext x y
  rw [← edgeOccurrences_pos,h x y]
  split_ifs <;> simp_all

lemma graphPartition_of_le_one (L : List (SimpleGraph V))
    (h : ∀ x y, edgeOccurrences L x y ≤ 1) : GraphPartition (graphUnion L) L := by
  intro x y
  have hh := h x y
  rw [← edgeOccurrences_pos]
  split_ifs <;> omega

lemma edgeOccurrences_sublist {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {L M : List (SimpleGraph V)} (h : L.Sublist M) (x y : V) :
    edgeOccurrences L x y ≤ edgeOccurrences M x y := by
  exact List.Sublist.countP_le h

lemma graphPartition_sublist {G : SimpleGraph V} {L M : List (SimpleGraph V)}
    (hp : GraphPartition G M) (h : L.Sublist M) : GraphPartition (graphUnion L) L := by
  apply graphPartition_of_le_one
  intro x y
  have hh := edgeOccurrences_sublist h x y
  rw [hp x y] at hh
  split_ifs at hh <;> omega

lemma StageSplit.ledger {P : AssignedPiece V} (s : StageSplit P) (x y : V) :
    edgeOccurrences (s.cycles ++ (s.boxes.flatMap s.pieces).map AssignedPiece.graph ++
      s.children.map AssignedPiece.graph) x y = if P.graph.Adj x y then 1 else 0 := by
  have h := s.partition x y
  rw [edgeOccurrences_append] at h
  rw [← edgeOccurrences_refine s.boxes AssignedPiece.graph
    (fun B => s.remainder B :: (s.pieces B).map AssignedPiece.graph) s.box_partition] at h
  have he : edgeOccurrences (s.boxes.flatMap (fun B => s.remainder B ::
      (s.pieces B).map AssignedPiece.graph)) x y =
      edgeOccurrences ((s.boxes.flatMap s.pieces).map AssignedPiece.graph) x y +
      edgeOccurrences (s.children.map AssignedPiece.graph) x y := by
    rw [s.children_map (fun _ G => G)]
    induction s.boxes with
    | nil => simp
    | cons B L ih =>
      simp only [List.flatMap_cons,List.map_append,List.map_cons,edgeOccurrences_append,
        edgeOccurrences_cons] at *
      omega
  rw [he] at h
  simpa only [edgeOccurrences_append,Nat.add_assoc] using h

lemma level_ledger (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (x y : V) :
    edgeOccurrences (levelCycles s j L ++ (levelPieces s j L).map AssignedPiece.graph ++
      (nextLayer s j L).map AssignedPiece.graph) x y = edgeOccurrences (L.map AssignedPiece.graph) x y := by
  induction L with
  | nil => simp [levelCycles,levelPieces,nextLayer]
  | cons P L ih =>
    have hp := (s j P).ledger x y
    simp only [levelCycles,levelPieces,nextLayer,List.flatMap_cons,List.map_append,
      List.map_cons,edgeOccurrences_append,edgeOccurrences_cons] at ih hp ⊢
    omega

lemma past_ledger (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) (x y : V) :
    edgeOccurrences (pastCycles s j k L ++ (pastPieces s j k L).map AssignedPiece.graph ++
      (advance s j k L).map AssignedPiece.graph) x y = edgeOccurrences (L.map AssignedPiece.graph) x y := by
  induction k with
  | zero => simp [pastCycles,pastPieces]
  | succ k ih =>
    have h := level_ledger s (j+k) (advance s j k L) x y
    simp only [pastCycles,pastPieces,advance_succ,List.map_append,edgeOccurrences_append] at ih h ⊢
    omega

lemma past_partition (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    GraphPartition P.graph (pastCycles s j k [P] ++ (pastPieces s j k [P]).map AssignedPiece.graph ++
      (advance s j k [P]).map AssignedPiece.graph) := by
  intro x y
  rw [past_ledger]
  simp

lemma levelCycles_good (s : SplitSystem V) (j) (L : List (AssignedPiece V)) :
    ∀ G ∈ levelCycles s j L, IsCycleGraph G := by
  intro G hG
  obtain ⟨P,_,hG⟩ := List.mem_flatMap.mp hG
  exact (s j P).cycles_good G hG

lemma pastCycles_good (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    ∀ G ∈ pastCycles s j k L, IsCycleGraph G := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih =>
    intro G hG
    rcases List.mem_append.mp hG with h | h
    · exact ih G h
    · exact levelCycles_good s (j+k) _ G h

lemma levelPieces_mass (s : SplitSystem V) (j) (L : List (AssignedPiece V)) :
    vertexMass (levelPieces s j L) ≤ vertexMass (nextLayer s j L) := by
  induction L with
  | nil => simp [levelPieces,nextLayer]
  | cons P L ih =>
    have hs : vertexMass ((s j P).boxes.flatMap (s j P).pieces) ≤ vertexMass (s j P).boxes := by
      rw [vertexMass_flatMap]
      unfold vertexMass
      exact List.sum_le_sum (fun B hB => (s j P).pieces_mass hB)
    simp only [levelPieces,nextLayer,List.flatMap_cons,vertexMass_append,
      StageSplit.children_mass] at ih ⊢
    linarith

lemma levelCycles_length (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (D : ℝ)
    (hb : ∀ P ∈ L, (s j P).Bounded D) :
    ((levelCycles s j L).length:ℝ) ≤ vertexMass L / (2*D^(1/100:ℝ)) := by
  induction L with
  | nil => simp [levelCycles]
  | cons P L ih =>
    have hp := (hb P (by simp)).1
    have hl := ih (fun Q hQ => hb Q (by simp [hQ]))
    simp only [levelCycles,List.flatMap_cons,List.length_append,Nat.cast_add,vertexMass_cons]
    rw [add_div]
    exact add_le_add hp hl

lemma pastPieces_mass (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    vertexMass (pastPieces s j k L) = ∑ l ∈ Finset.range k,
      vertexMass (levelPieces s (j+l) (advance s j l L)) := by
  induction k with
  | zero => simp [pastPieces]
  | succ k ih => simp [pastPieces,ih,Finset.sum_range_succ]

lemma pastCycles_length (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    ((pastCycles s j k L).length:ℝ) = ∑ l ∈ Finset.range k,
      ((levelCycles s (j+l) (advance s j l L)).length:ℝ) := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih => simp [pastCycles,ih,Finset.sum_range_succ]

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale

noncomputable section
open SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

lemma decompositionCost_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G ≤ Nat.card G.edgeSet := decompositionCost_le (edgeDecomposition_singleEdges G)

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai.Scale
namespace ErdosGallai.Scale
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

lemma decompositionCost_assemble_same {V J : Type} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ ∑ j, decompositionCost (H j) := by
  simpa using decompositionCost_adjoin_same (I := Empty) G Empty.elim (fun i => nomatch i)
    (by intro i; exact i.elim) H hHG hHH (fun _ i => nomatch i) (by simpa using hu)

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_pairwise_get {A : Type cycleUniverse1} {R : A → A → Prop} {L : List A}
    (h : L.Pairwise R) (hs : (∀ ⦃left right⦄, R left right → R right left)) : Pairwise fun i j : Fin L.length => R (L.get i) (L.get j) := by
  intro i j hij
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Fin.ext he)) with hlt | hgt
  · exact List.pairwise_iff_getElem.mp h i.val j.val i.isLt j.isLt hlt
  · exact hs (List.pairwise_iff_getElem.mp h j.val i.val j.isLt i.isLt hgt)

lemma list_sum_get {A : Type cycleUniverse2} {M : Type cycleUniverse3} [AddCommMonoid M] (L : List A) (f : A → M) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  calc
    _ = (List.map f (List.ofFn L.get)).sum := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

lemma graphPartition_pairwise {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : L.Pairwise fun H K => Disjoint H.edgeSet K.edgeSet := by
  induction L generalizing G with
  | nil => simp
  | cons H L ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih (graphPartition_sublist h (List.sublist_cons_self _ _))⟩
    intro K hK
    apply Set.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.ind with
    | _ x y =>
      have hc := h x y
      have hp : 0 < edgeOccurrences L x y := by
        rw [edgeOccurrences_pos,graphUnion_adj]
        exact ⟨K,hK,he'⟩
      have hxy : H.Adj x y := he
      simp only [edgeOccurrences_cons,hxy,ite_true] at hc
      split_ifs at hc <;> omega

lemma graphUnion_edges (L : List (SimpleGraph V)) :
    (⋃ i : Fin L.length, (L.get i).edgeSet) = (graphUnion L).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet]

    rw [graphUnion_adj]
    constructor
    · rintro ⟨i,h⟩; exact ⟨_,L.get_mem i,h⟩
    · rintro ⟨H,hH,h⟩
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
      exact ⟨i,h⟩

lemma decompositionCost_partition {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : decompositionCost G ≤ (L.map decompositionCost).sum := by
  rw [← list_sum_get L decompositionCost]
  apply decompositionCost_assemble_same G (fun i : Fin L.length => L.get i)
  · intro i; exact partition_member_le h (L.get_mem i)
  · exact list_pairwise_get (graphPartition_pairwise h) (fun _ _ h => h.symm)
  · rw [graphUnion_edges,graphPartition_union h]

lemma decompositionCost_cycle {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} (h : IsCycleGraph G) :
    decompositionCost G ≤ 1 := by
  apply decompositionCost_le
  have hp : CycleOrSingleEdge G G.edgeSet := by
    obtain ⟨a,p,hp,he⟩ := h
    exact Or.inl ⟨a,p,hp,he⟩
  refine ⟨fun _ => G.edgeSet,fun _ => hp,?_,?_⟩
  · intro i j hij; exact False.elim (hij (Subsingleton.elim i j))
  · ext e
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨(0 : Fin 1),h⟩⟩

lemma decompositionCost_edgeCount {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) : decompositionCost G ≤ edgeCount G := by
  have h := decompositionCost_singleEdges G
  rw [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet] at h
  exact h

lemma decompositionCost_partition_real {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : (decompositionCost G:ℝ) ≤
      (L.map (fun H => (decompositionCost H:ℝ))).sum := by
  have hh : (decompositionCost G:ℝ) ≤ ((L.map decompositionCost).sum:ℕ) :=
    Nat.cast_le.mpr (decompositionCost_partition h)
  simpa [List.map_map,Function.comp_def] using hh

lemma decompositionCost_cycles (L : List (SimpleGraph V))
    (h : ∀ G ∈ L, IsCycleGraph G) :
    (L.map (fun H => (decompositionCost H:ℝ))).sum ≤ L.length := by
  calc
    _ ≤ (L.map (fun _ => (1:ℝ))).sum := List.sum_le_sum (fun G hG => by exact_mod_cast decompositionCost_cycle (h G hG))
    _ = _ := by simp

end
end ErdosGallai.Scale

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.PrefixSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai
noncomputable section
open Finset

theorem prefix_selection (S : ℕ → ℝ) (hS : ∀ j, 0 ≤ S j) (K N : ℕ)
    (hsupp : ∀ j, N ≤ j → S j = 0) (hne : ∃ j, 0 < S j) :
    ∃ i, 0 < S i ∧ ∑ j ∈ range (i+K+1), S j ≤ 4*(K+1:ℝ)*S i := by
  let A := (range N).filter (fun j => 0 < S j)
  have hA : A.Nonempty := by
    obtain ⟨j,hj⟩ := hne
    exact ⟨j, by
      simp only [A, mem_filter, mem_range]
      exact ⟨by by_contra hn; rw [hsupp j (by omega)] at hj; linarith, hj⟩⟩
  let i₀ := A.min' hA
  have hi₀A : i₀ ∈ A := A.min'_mem hA
  have hi₀pos : 0 < S i₀ := (mem_filter.mp hi₀A).2
  have hstart : (∑ j ∈ range (i₀+1), S j) = S i₀ := by
    apply sum_eq_single i₀
    · intro j hj hji
      by_contra hjzero
      have hjpos : 0 < S j := lt_of_le_of_ne (hS j) (Ne.symm hjzero)
      have hjA : j ∈ A := by
        simp only [A, mem_filter, mem_range]
        refine ⟨?_, hjpos⟩
        have hiN := (mem_range.mp (mem_filter.mp hi₀A).1)
        have hjle := mem_range.mp hj
        omega
      have hmin : i₀ ≤ j := A.min'_le j hjA
      have hjle := mem_range.mp hj
      omega
    · intro hi
      exact (hi (by simp)).elim
  let B := A.filter (fun i => (∑ j ∈ range (i+1), S j) ≤ 2*(K+1:ℝ)*S i)
  have hB : B.Nonempty := by
    refine ⟨i₀, mem_filter.mpr ⟨hi₀A, ?_⟩⟩
    rw [hstart]
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  let i := B.max' hB
  have hiB : i ∈ B := B.max'_mem hB
  have hiA : i ∈ A := (mem_filter.mp hiB).1
  have hipos : 0 < S i := (mem_filter.mp hiA).2
  have hinv : (∑ j ∈ range (i+1), S j) ≤ 2*(K+1:ℝ)*S i := (mem_filter.mp hiB).2
  refine ⟨i, hipos, ?_⟩
  by_contra hfail
  have hfail' : 4*(K+1:ℝ)*S i < ∑ j ∈ range (i+K+1), S j := lt_of_not_ge hfail
  have hwindow : 2*(K+1:ℝ)*S i < ∑ j ∈ Ico (i+1) (i+K+1), S j := by
    have hsplit := Finset.sum_range_add_sum_Ico S (by omega : i+1 ≤ i+K+1)
    linarith
  have hwindow_nonempty : (Ico (i+1) (i+K+1)).Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty.mp hh] at hwindow
    simp only [sum_empty] at hwindow
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  obtain ⟨j,hjw,hmax⟩ := Finset.exists_max_image (Ico (i+1) (i+K+1)) S hwindow_nonempty
  have hsum : (∑ l ∈ Ico (i+1) (i+K+1), S l) ≤ (K:ℝ)*S j := by
    calc
      _ ≤ ∑ _l ∈ Ico (i+1) (i+K+1), S j := sum_le_sum hmax
      _ = _ := by simp []
  have hdouble : 2*S i < S j := by
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hjpos : 0 < S j := by linarith
  have hjA : j ∈ A := by
    simp only [A, mem_filter, mem_range]
    exact ⟨by by_contra hjN; rw [hsupp j (by omega)] at hjpos; linarith, hjpos⟩
  have hjbounds := Finset.mem_Ico.mp hjw
  have hpartial : (∑ l ∈ Ico (i+1) (j+1), S l) ≤ (K:ℝ)*S j := by
    calc
      _ ≤ ∑ l ∈ Ico (i+1) (i+K+1), S l := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [mem_Ico] at hl ⊢
          omega
        · intro l _ _; exact hS l
      _ ≤ _ := hsum
  have hjinv : (∑ l ∈ range (j+1), S l) ≤ 2*(K+1:ℝ)*S j := by
    have hsplit := Finset.sum_range_add_sum_Ico S (by omega : i+1 ≤ j+1)
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hjB : j ∈ B := mem_filter.mpr ⟨hjA,hjinv⟩
  have hji : j ≤ i := B.le_max' j hjB
  omega

end
end ErdosGallai

end

end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CostRegrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma StageSplit.rest_graph {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) {B} (hB : B ∈ s.boxes) :
    (s.rest B).graph = s.remainder B := by simp [StageSplit.rest,hB]
lemma StageSplit.children_eq_map_rest {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) :
    s.children = s.boxes.map s.rest := by
  unfold StageSplit.children
  rw [← List.pmap_eq_map (f := s.rest) (fun B (hB : B ∈ s.boxes) => hB)]
  apply List.pmap_congr_left
  intro B hB
  simp [StageSplit.rest,hB]

lemma pastPieces_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse1}
    (L : List I) (f : I → List (AssignedPiece V)) :
    (pastPieces s j k (L.flatMap f)).Perm (L.flatMap (fun i => pastPieces s j k (f i))) := by
  induction k with
  | zero => simp [pastPieces]
  | succ k ih =>
    simp only [pastPieces,advance_flatMap,levelPieces,List.flatMap_assoc]
    apply (ih.append_right _).trans
    exact List.flatMap_append_perm _ _ _
lemma pastCycles_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse2}
    (L : List I) (f : I → List (AssignedPiece V)) :
    (pastCycles s j k (L.flatMap f)).Perm (L.flatMap (fun i => pastCycles s j k (f i))) := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih =>
    simp only [pastCycles,advance_flatMap,levelCycles,List.flatMap_assoc]
    apply (ih.append_right _).trans
    exact List.flatMap_append_perm _ _ _

lemma pastPieces_add (s : SplitSystem V) (j k l) (L : List (AssignedPiece V)) :
    pastPieces s j (k+l) L = pastPieces s j k L ++ pastPieces s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp [pastPieces]
  | succ l ih => simp [pastPieces,ih,advance_add,Nat.add_assoc,List.append_assoc]
lemma pastCycles_add (s : SplitSystem V) (j k l) (L : List (AssignedPiece V)) :
    pastCycles s j (k+l) L = pastCycles s j k L ++ pastCycles s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp [pastCycles]
  | succ l ih => simp [pastCycles,ih,advance_add,Nat.add_assoc,List.append_assoc]

lemma advance_mem_mono (s : SplitSystem V) (j k) {L M : List (AssignedPiece V)}
    (h : ∀ P ∈ L, P ∈ M) : ∀ Q ∈ advance s j k L, Q ∈ advance s j k M := by
  induction k with
  | zero => exact h
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    exact (nextLayer_mem s (j+k) _ Q).mpr ⟨P,ih P hP,B,hB,hv,hg⟩

lemma advance_local_mem (s : SplitSystem V) (i k) (L : List (AssignedPiece V))
    {P B : AssignedPiece V} (hP : P ∈ advance s 0 i L) (hB : B ∈ (s i P).boxes) :
    ∀ Q ∈ advance s (i+1) k [(s i P).rest B], Q ∈ advance s 0 (i+1+k) L := by
  rw [advance_add, Nat.zero_add]
  apply advance_mem_mono
  intro Q hQ
  simp only [List.mem_singleton] at hQ
  subst Q
  simp only [advance_succ,Nat.zero_add]

  apply (nextLayer_mem s i _ _).mpr
  exact ⟨P,hP,B,hB,(s i P).rest_vertices B,(s i P).rest_graph hB⟩

lemma box_regroup {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) :
    GraphPartition B.graph
      (pastCycles s j k [R] ++ (pastPieces s j k [R]).map AssignedPiece.graph ++
        [graphUnion ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph)]) := by
  let L := (advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph
  have hL : GraphPartition (graphUnion L) L := by
    apply graphPartition_of_le_one
    intro x y
    have hb := hBR x y
    have hr := past_partition s j k R x y
    simp only [edgeOccurrences_cons,edgeOccurrences_append] at hb hr ⊢
    dsimp only [L]
    rw [edgeOccurrences_append]
    split_ifs at hb hr <;> omega
  intro x y
  have hb := hBR x y
  have hr := past_partition s j k R x y
  have hl := hL x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append,edgeOccurrences_nil,Nat.add_zero] at hb hr hl ⊢
  dsimp only [L] at hl
  rw [edgeOccurrences_append] at hl
  omega

lemma piece_list_cost (L : List (AssignedPiece V)) (c : ℝ)
    (h : ∀ P ∈ L, (decompositionCost P.graph:ℝ) ≤ c*P.vertices.card) :
    (L.map (fun P => (decompositionCost P.graph:ℝ))).sum ≤ c*vertexMass L := by
  induction L with
  | nil => simp
  | cons P L ih =>
    have hp := h P (by simp)
    have hl := ih (fun Q hQ => h Q (by simp [hQ]))
    simp only [List.map_cons,List.sum_cons,vertexMass_cons]
    nlinarith

lemma box_cost_regroup {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) (c q : ℝ)
    (hp : ∀ P ∈ pastPieces s j k [R], (decompositionCost P.graph:ℝ) ≤ c*P.vertices.card)
    (hq : (decompositionCost (graphUnion ((advance s j k [R]).map AssignedPiece.graph ++
      A.map AssignedPiece.graph)):ℝ) ≤ q) :
    (decompositionCost B.graph:ℝ) ≤ (pastCycles s j k [R]).length +
      c*vertexMass (pastPieces s j k [R]) + q := by
  have hh := decompositionCost_partition_real (box_regroup A hBR s j k)
  have hc := decompositionCost_cycles (pastCycles s j k [R]) (pastCycles_good s j k [R])
  have hm := piece_list_cost (pastPieces s j k [R]) c hp
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,List.map_map,Function.comp_def] at hh
  linarith

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Real Filter

lemma mainP_pos : 0 < mainP := by norm_num [mainP]
lemma mainEta_pos : 0 < mainEta := by norm_num [mainEta,mainP]
lemma mainH_pos : 0 < mainH := by unfold mainH; exact div_pos (by norm_num) (pow_pos Scale.scaleTheta_pos _)
lemma mainA₁_nonneg : 0 ≤ mainA₁ := by unfold mainA₁; linarith [mainH_pos]
lemma mainA₂_nonneg : 0 ≤ mainA₂ := by unfold mainA₂; exact (by norm_num [mainP] : (0:ℝ) ≤ 9*mainP+8).trans (le_max_left _ _)

lemma eventually_inverse_power_log (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C*D^(-ε) ≤ 1/logb 2 D := by
  filter_upwards [Batch.eventually_logb_le_power (ε/2) (by positivity),
    Batch.eventually_const_mul_power_le C (ε/2) ε (by linarith),
    eventually_gt_atTop (1:ℝ)] with D hl hc hD
  have hd : 0 < D := by linarith
  have hw : 0 < logb 2 D := Real.logb_pos (by norm_num) hD
  have hp : 0 < D^ε := Real.rpow_pos_of_pos hd _
  apply (le_div_iff₀ hw).mpr
  calc
    _ = (C*logb 2 D)/D^ε := by rw [Real.rpow_neg hd.le]; ring
    _ ≤ 1 := (div_le_one hp).mpr ((mul_le_mul_of_nonneg_left hl hC).trans hc)

lemma main_scale_ready_cutoff (wmin : ℝ) : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, MainScaleReady wmin D := by
  have hev : ∀ᶠ D : ℝ in atTop, MainScaleReady wmin D := by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Real.tendsto_logb_atTop (by norm_num : (1:ℝ) < 2)).eventually (eventually_ge_atTop wmin),
      eventually_inverse_power_log 1 (1/100) (by norm_num) (by norm_num),
      Batch.eventually_const_mul_power_le 2 (1/1000) (3/10) (by norm_num),
      eventually_inverse_power_log 2 (9/1000) (by norm_num) (by norm_num),
      eventually_inverse_power_log 2 (87/100) (by norm_num) (by norm_num),
      eventually_inverse_power_log 8 (3/20) (by norm_num) (by norm_num),
      Batch.eventually_constant_le_power 8 (3/100) (by norm_num)] with D hD hw hc hb hbad hs₁ hs₂ h8
    refine ⟨hD,hw,?_,by linarith,by simpa only [neg_div] using hbad,?_,h8⟩
    · simpa only [one_mul,Real.rpow_neg (by linarith : 0 ≤ D),one_div] using hc
    · simp only [neg_div]
      linarith
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2,lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _),?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai

end

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma costMass_bound (L : List (AssignedPiece V)) (f : AssignedPiece V → ℝ)
    (h : ∀ P ∈ L, (decompositionCost P.graph:ℝ) ≤ f P) : costMass L ≤ (L.map f).sum :=
  List.sum_le_sum h

lemma past_cost (s : SplitSystem V) (j k) (P : AssignedPiece V) (c : ℝ)
    (hp : ∀ Q ∈ pastPieces s j k [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s j k [P]).length:ℝ) +
      c*vertexMass (pastPieces s j k [P]) + costMass (advance s j k [P]) := by
  have hh := decompositionCost_partition_real (past_partition s j k P)
  have hc := decompositionCost_cycles _ (pastCycles_good s j k [P])
  have hm := piece_list_cost _ c hp
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at hh
  dsimp only [costMass]
  linarith

lemma stage_cost (s : SplitSystem V) (j) (P : AssignedPiece V) :
    (decompositionCost P.graph:ℝ) ≤ ((s j P).cycles.length:ℝ) + costMass (s j P).boxes := by
  have hh := decompositionCost_partition_real (s j P).partition
  have hc := decompositionCost_cycles _ (s j P).cycles_good
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at hh
  dsimp only [costMass]
  linarith

lemma vertexMass_perm {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {L M : List (AssignedPiece V)} (h : L.Perm M) : vertexMass L = vertexMass M :=
  (h.map _).sum_eq

lemma pastCycles_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => ((pastCycles s j k [P]).length:ℝ))).sum = ((pastCycles s j k L).length:ℝ) := by
  have h := (pastCycles_flatMap s j k L (fun P => [P])).length_eq
  simp only [List.flatMap_singleton'] at h
  rw [h,List.length_flatMap]
  simp [Function.comp_def]

lemma pastPieces_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => vertexMass (pastPieces s j k [P]))).sum = vertexMass (pastPieces s j k L) := by
  have h := vertexMass_perm (pastPieces_flatMap s j k L (fun P => [P]))
  simpa only [List.flatMap_singleton',vertexMass_flatMap] using h.symm

lemma advance_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => vertexMass (advance s j k [P]))).sum = vertexMass (advance s j k L) := by
  have h := congrArg vertexMass (advance_flatMap s j k L (fun P => [P]))
  simpa only [List.flatMap_singleton',vertexMass_flatMap] using h.symm

lemma pastCycles_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (pastCycles s j (k+1) [P]).Perm ((s j P).cycles ++
      (s j P).boxes.flatMap (fun B => pastCycles s (j+1) k [(s j P).rest B])) := by
  rw [show k+1=1+k by omega,pastCycles_add]
  simp only [pastCycles,advance_zero,List.nil_append,levelCycles,List.flatMap_singleton,
    Nat.add_zero,advance_succ,nextLayer,Nat.add_zero,List.flatMap_singleton,StageSplit.children_eq_map_rest]
  have hh := pastCycles_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])
  simp only [← List.map_eq_flatMap] at hh
  exact hh.append_left _

lemma pastPieces_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (pastPieces s j (k+1) [P]).Perm ((s j P).boxes.flatMap (s j P).pieces ++
      (s j P).boxes.flatMap (fun B => pastPieces s (j+1) k [(s j P).rest B])) := by
  rw [show k+1=1+k by omega,pastPieces_add]
  simp only [pastPieces,advance_zero,List.nil_append,levelPieces,List.flatMap_singleton,
    Nat.add_zero,advance_succ,nextLayer,Nat.add_zero,List.flatMap_singleton,StageSplit.children_eq_map_rest]
  have hh := pastPieces_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])
  simp only [← List.map_eq_flatMap] at hh
  exact hh.append_left _

lemma advance_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    advance s j (k+1) [P] = (s j P).boxes.flatMap (fun B => advance s (j+1) k [(s j P).rest B]) := by
  rw [show k+1=1+k by omega,advance_add]
  simp only [advance_succ,advance_zero,Nat.add_zero,nextLayer,List.flatMap_singleton,
    StageSplit.children_eq_map_rest]
  simpa only [← List.map_eq_flatMap] using advance_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])

lemma selected_input_cost (s : SplitSystem V) (j k) (P : AssignedPiece V) (c α β γ : ℝ)
    (hp : ∀ B ∈ (s j P).boxes, ∀ Q ∈ pastPieces s (j+1) k [(s j P).rest B],
      (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card)
    (hq : ∀ B ∈ (s j P).boxes,
      (decompositionCost (graphUnion ((advance s (j+1) k [(s j P).rest B]).map AssignedPiece.graph ++
        ((s j P).pieces B).map AssignedPiece.graph)):ℝ) ≤
      c*vertexMass ((s j P).pieces B) + α*vertexMass (advance s (j+1) k [(s j P).rest B]) +
      β*vertexMass ((s j P).pieces B) + γ*B.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s j (k+1) [P]).length:ℝ) +
      c*vertexMass (pastPieces s j (k+1) [P]) + α*vertexMass (advance s j (k+1) [P]) +
      β*vertexMass (levelPieces s j [P]) + γ*vertexMass (nextLayer s j [P]) := by
  have hb (B) (hB : B ∈ (s j P).boxes) := box_cost_regroup ((s j P).pieces B)
    (R := (s j P).rest B) (by simpa only [StageSplit.rest_graph _ hB] using (s j P).box_partition B hB)
    s (j+1) k c _ (hp B hB) (hq B hB)
  have hh := (stage_cost s j P).trans (add_le_add (le_refl _) (costMass_bound _ _ hb))
  have hc := (pastCycles_after_first s j k P).length_eq
  have hm := vertexMass_perm (pastPieces_after_first s j k P)
  rw [hc,List.length_append,Nat.cast_add,List.length_flatMap,hm,vertexMass_append,
    vertexMass_flatMap,vertexMass_flatMap,advance_after_first,vertexMass_flatMap]
  simp only [levelPieces,nextLayer,List.flatMap_singleton,StageSplit.children_mass,vertexMass_flatMap]
  simp only [List.sum_map_add,List.sum_map_mul_left] at hh
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def,vertexMass] at hh ⊢
  linarith

lemma selected_prefix_cost (s : SplitSystem V) (i k) (P : AssignedPiece V) (c α β γ : ℝ)
    (hp : ∀ Q ∈ pastPieces s 0 (i+(k+1)) [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card)
    (hq : ∀ Q ∈ advance s 0 i [P], ∀ B ∈ (s i Q).boxes,
      (decompositionCost (graphUnion ((advance s (i+1) k [(s i Q).rest B]).map AssignedPiece.graph ++
        ((s i Q).pieces B).map AssignedPiece.graph)):ℝ) ≤
      c*vertexMass ((s i Q).pieces B) + α*vertexMass (advance s (i+1) k [(s i Q).rest B]) +
      β*vertexMass ((s i Q).pieces B) + γ*B.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s 0 (i+(k+1)) [P]).length:ℝ) +
      c*vertexMass (pastPieces s 0 (i+(k+1)) [P]) + α*vertexMass (advance s 0 (i+(k+1)) [P]) +
      β*vertexMass (levelPieces s i (advance s 0 i [P])) + γ*vertexMass (advance s 0 (i+1) [P]) := by
  have he : pastPieces s 0 (i+(k+1)) [P] = pastPieces s 0 i [P] ++
      pastPieces s i (k+1) (advance s 0 i [P]) := by rw [pastPieces_add,Nat.zero_add]
  have hp₀ : ∀ Q ∈ pastPieces s 0 i [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card := by
    intro Q hQ; apply hp; rw [he]; exact List.mem_append_left _ hQ
  have hpp (Q) (hQ : Q ∈ advance s 0 i [P]) (B) (hB : B ∈ (s i Q).boxes)
      (R) (hR : R ∈ pastPieces s (i+1) k [(s i Q).rest B]) :
      (decompositionCost R.graph:ℝ) ≤ c*R.vertices.card := by
    apply hp R
    rw [he,List.mem_append]
    right
    have h₁ := pastPieces_flatMap s i (k+1) (advance s 0 i [P]) (fun Q => [Q])
    simp only [List.flatMap_singleton'] at h₁
    rw [h₁.mem_iff]
    apply List.mem_flatMap.mpr
    refine ⟨Q,hQ,?_⟩
    rw [(pastPieces_after_first s i k Q).mem_iff,List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨B,hB,hR⟩)
  have hh := (past_cost s 0 i P c hp₀).trans (add_le_add (le_refl _)
    (costMass_bound _ _ (fun Q hQ => selected_input_cost s i k Q c α β γ (hpp Q hQ) (hq Q hQ))))
  rw [pastCycles_add,pastPieces_add,advance_add,Nat.zero_add,List.length_append,Nat.cast_add,vertexMass_append]
  simp only [List.sum_map_add,List.sum_map_mul_left,pastCycles_sum,pastPieces_sum,advance_sum] at hh
  have hS : ((advance s 0 i [P]).map (fun Q => vertexMass (levelPieces s i [Q]))).sum =
      vertexMass (levelPieces s i (advance s 0 i [P])) := by
    simp only [levelPieces,List.flatMap_singleton,vertexMass_flatMap]
  have hN : ((advance s 0 i [P]).map (fun Q => vertexMass (nextLayer s i [Q]))).sum =
      vertexMass (advance s 0 (i+1) [P]) := by
    simp only [nextLayer,List.flatMap_singleton,advance_succ,Nat.zero_add,vertexMass_flatMap]
  rw [hS,hN] at hh
  linarith

end
end ErdosGallai.Scale

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.UniformLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem uniform_layers : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V),
    Dstar ≤ (P.vertices.card:ℝ) → 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ P.vertices.card →
    Nonempty (Layers P Dstar) := by
  obtain ⟨Dsp,hsp⟩ := scale_splitter
  refine ⟨max Dsp 2,lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _),?_⟩
  intro Dstar hD V _ _ P hn hdeg
  have hD1 : 1 < Dstar := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) ((le_max_right _ _).trans hD)
  have hn1 : 1 < (P.vertices.card:ℝ) := hD1.trans_le hn
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  obtain ⟨split,hsplit⟩ := hsp V
  let s : SplitSystem V := fun j Q => split (inductionScale P.vertices.card j) Q
  have hs : ∀ j Q, Dstar ≤ inductionScale P.vertices.card j → Q.vertices.Nonempty →
      2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j →
      (s j Q).Bounded (inductionScale P.vertices.card j) := by
    intro j Q hj hQ hd
    exact hsplit _ ((le_max_left _ _).trans (hD.trans hj)) Q hQ hd
  obtain ⟨m,hm,hlast,hcut⟩ := inductionScale_first_cutoff P.vertices.card Dstar hD1 hn
  have hL : ∀ Q ∈ [P], Q.vertices.Nonempty := by simpa using hne
  have hLd : ∀ Q ∈ [P], 2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card 0 := by
    simpa only [List.mem_singleton,forall_eq,inductionScale_zero] using hdeg
  refine ⟨{ system := s, count := m, positive := hm, cutoff := hcut, last_lt := hlast, bounded := ?_, degree := ?_ }⟩
  · intro j hj
    simpa only [Nat.zero_add] using advance_bounded s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))
  · intro j hj
    simpa only [Nat.zero_add] using advance_valid s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))

variable {P : AssignedPiece V} {Dstar : ℝ}

lemma Layers.mass_lower (H : Layers P Dstar) (j) : (P.vertices.card:ℝ) ≤ H.mass j :=
  advance_mass_lower H.system 0 j P

lemma Layers.mass_upper (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (j) (hj : j < H.count) :
    H.mass (j+1) ≤ (1+80/logb 2 (H.scale j))*P.vertices.card := by
  have hh := advance_mass_global_product H.system P.vertices.card hn 0 (j+1) [P]
    (fun l hl => by simpa only [Nat.zero_add] using H.bounded l (by omega))
  have hx := scale_overlap_product P.vertices.card 2 hn (by norm_num) j (by norm_num; exact hlog j hj)
  simp only [Nat.zero_add,vertexMass_cons,vertexMass_nil,add_zero] at hh
  have hx' := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)
  norm_num only [show (40:ℝ)*2=80 by norm_num] at hx'
  dsimp only [Layers.mass,Layers.frontier,Layers.scale] at *
  nlinarith

lemma Layers.mass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (k) (hk : k ≤ H.count) :
    H.mass k ≤ 2*P.vertices.card := by
  cases k with
  | zero => simp only [Layers.mass,Layers.frontier,advance_zero,vertexMass_cons,vertexMass_nil,add_zero]; nlinarith [(Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)]
  | succ j =>
    have hj : j < H.count := by omega
    have hh := H.mass_upper hn hlog j hj
    have hl := hlog j hj
    have hd : 80/logb 2 (H.scale j) ≤ 1 := (div_le_one (by linarith)).mpr hl
    have hc : (0:ℝ) ≤ P.vertices.card := Nat.cast_nonneg _
    nlinarith

lemma Layers.pieceMass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (j) (hj : j < H.count) :
    H.pieceMass j ≤ 2*P.vertices.card :=
  (levelPieces_mass H.system j (H.frontier j)).trans (by
    simpa only [Layers.mass,Layers.frontier,advance_succ,Nat.zero_add] using H.mass_two hn hlog (j+1) (by omega))

lemma Layers.cycles_bound (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (j) (hj : j < H.count) :
    ((pastCycles H.system 0 (j+1) [P]).length:ℝ) ≤ 20*P.vertices.card/logb 2 (H.scale j) := by
  rw [pastCycles_length]
  apply (Finset.sum_le_sum (fun l hl => ?_)).trans
    (scale_prefix_cycle_cost P.vertices.card hn j (fun l => H.mass l)
      (fun l hl => H.mass_two hn (fun a ha => (hready a ha).log_large) l (by have := Finset.mem_range.mp hl; omega))
      (fun l hl => (hready l (by have := Finset.mem_range.mp hl; omega)).cycle_power))
  simpa only [Nat.zero_add] using levelCycles_length H.system l (H.frontier l) (H.scale l)
    (H.bounded l (by have := Finset.mem_range.mp hl; omega))

lemma Layers.subset (H : Layers P Dstar) (j) : ∀ Q ∈ H.frontier j, Q.vertices ⊆ P.vertices :=
  advance_subset H.system 0 j [P] P.vertices (by simp)

lemma Layers.box_subset (H : Layers P Dstar) (j) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier j) (hB : B ∈ (H.system j Q).boxes) : B.vertices ⊆ P.vertices :=
  ((H.system j Q).box_subset B hB).trans (H.subset j Q hQ)

lemma Layers.boundary_order (H : Layers P Dstar) (j) (hj : j < H.count)
    {Q : AssignedPiece V} (hQ : Q ∈ H.frontier (j+1)) :
    (Q.vertices.card:ℝ) ≤ (H.scale j)^(51/50:ℝ) := by
  simp only [Layers.frontier,advance_succ,Nat.zero_add] at hQ
  obtain ⟨T,hT,B,hB,hv,_⟩ := (nextLayer_mem H.system j _ Q).mp hQ
  rw [hv]
  exact (H.bounded j hj T hT).2.2.1 B hB

lemma Layers.local_mass (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (i k)
    (hik : i+k < H.count) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes) :
    vertexMass (advance H.system (i+1) k [(H.system i Q).rest B]) ≤
      (1+80/logb 2 (H.scale (i+k)))*B.vertices.card := by
  have hh := advance_mass_global_product H.system P.vertices.card hn (i+1) k [(H.system i Q).rest B]
    (fun l hl R hR => by
      have hr := advance_local_mem H.system i l [P] hQ hB R hR
      have he : i+1+l = (i+l)+1 := by omega
      exact H.bounded (i+1+l) (by omega) R hr)
  have hx := scale_overlap_product P.vertices.card 2 hn (by norm_num) (i+k)
    (by norm_num; exact hlog (i+k) hik)
  simp only [vertexMass_cons,vertexMass_nil,add_zero,StageSplit.rest_vertices] at hh
  rw [show i+1+k=(i+k)+1 by omega] at hh
  have hx' := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg B.vertices.card : (0:ℝ) ≤ _)
  norm_num only [show (40:ℝ)*2=80 by norm_num] at hx'
  dsimp only [Layers.scale] at *
  nlinarith

lemma Layers.local_mass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (i k)
    (hik : i+k < H.count) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes) :
    vertexMass (advance H.system (i+1) k [(H.system i Q).rest B]) ≤ 2*B.vertices.card := by
  have hh := H.local_mass hn hlog i k hik hQ hB
  have hl := hlog (i+k) hik
  have hd : 80/logb 2 (H.scale (i+k)) ≤ 1 := (div_le_one (by linarith)).mpr hl
  have hc : (0:ℝ) ≤ B.vertices.card := Nat.cast_nonneg _
  nlinarith

lemma Layers.gap_order (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i)
    (hik : i+200 < H.count) {Q B R : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes)
    (hR : R ∈ advance H.system (i+1) 200 [(H.system i Q).rest B]) :
    (R.vertices.card:ℝ) ≤ (H.scale i)^(1/1000:ℝ) ∧
      2*(edgeCount R.graph:ℝ)/R.vertices.card ≤ (H.scale i)^(1/1000:ℝ) := by
  have hr := advance_local_mem H.system i 200 [P] hQ hB R hR
  have hr' : R ∈ H.frontier ((i+200)+1) := by convert hr using 1
  have hd : 1 < H.scale i := inductionScale_gt_one P.vertices.card hn i
  constructor
  · have hh := H.boundary_order (i+200) hik hr'
    apply hh.trans
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity),← Real.rpow_mul (by linarith : 0 ≤ inductionScale P.vertices.card i)]
    apply Real.rpow_le_rpow_of_exponent_le hd.le
    nlinarith [inductionScale_window.1]
  · have hh := H.degree ((i+200)+1) (by omega) R hr'
    apply hh.trans
    rw [show i+200+1=i+201 by omega]
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hd.le inductionScale_window.2.le

end
end ErdosGallai.Scale

end

end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.LayerCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma box_coupled_partition {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) :
    GraphPartition (graphUnion ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph))
      ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph) := by
  apply graphPartition_of_le_one
  intro x y
  have hb := hBR x y
  have hr := past_partition s j k R x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append] at hb hr ⊢
  split_ifs at hb hr <;> omega

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem uniform_gap_prefix_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] (P : AssignedPiece V) (H : Layers P Dstar),
    1 < (P.vertices.card:ℝ) →
    (∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) →
    ∀ i, i+200 < H.count → ∀ C t : ℝ, 0 ≤ C → 0 ≤ t →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (ErdosGallai.decompositionCost G:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (Fintype.card Q:ℝ) ≤ (H.scale i)^(3/10:ℝ) →
      (Batch.decompositionCost G:ℝ) ≤ t*Fintype.card Q) →
    (∀ R ∈ pastPieces H.system 0 (i+201) [P],
      (decompositionCost R.graph:ℝ) ≤ (9+C*ErdosGallai.mainEta)*R.vertices.card) →
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles H.system 0 (i+201) [P]).length:ℝ) +
      (9+C*ErdosGallai.mainEta)*vertexMass (pastPieces H.system 0 (i+201) [P]) +
      (t+8)*H.mass (i+201) + (8-t/3)*H.pieceMass i +
      ((2/3)*t/logb 2 (H.scale i)-8)*H.mass (i+1) := by
  obtain ⟨D₀,hD₀,hlocal⟩ := uniform_local_box_cost
  refine ⟨D₀,hD₀,?_⟩
  intro Dstar hD V _ P H hn hready i hik C t hC ht ih ihq hp
  have hi : i < H.count := by omega
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  have hsmall : (H.scale i)^(3/10:ℝ) < (P.vertices.card:ℝ) := by
    apply lt_of_lt_of_le _ (inductionScale_le P.vertices.card hn.le i)
    have hd := inductionScale_gt_one P.vertices.card hn i
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hd (by norm_num : (3/10:ℝ) < 1)
  apply selected_prefix_cost H.system i 200 P (9+C*ErdosGallai.mainEta)
    (t+8) (8-t/3) ((2/3)*t/logb 2 (H.scale i)-8) hp
  intro Q hQ B hB
  have hQne := advance_nonempty H.system 0 i [P] (by simpa using hne) Q hQ
  have hBne := (H.system i Q).box_nonempty hQne B hB
  have hrest : ((H.system i Q).rest B).vertices.Nonempty := by simpa only [StageSplit.rest_vertices] using hBne
  exact hlocal (H.scale i) (hD.trans (H.cutoff i hi)) 80 (hready i hi) V
    (advance H.system (i+1) 200 [(H.system i Q).rest B]) ((H.system i Q).pieces B) B.vertices
    (box_coupled_partition _ (by simpa only [StageSplit.rest_graph _ hB] using (H.system i Q).box_partition B hB) _ _ _)
    ((H.system i Q).piece_disjoint B hB) ((H.system i Q).piece_subset B hB)
    (advance_subset H.system (i+1) 200 [(H.system i Q).rest B] B.vertices (by simp))
    (fun v hv => advance_cover H.system (i+1) 200 [(H.system i Q).rest B] ((H.system i Q).rest B) (by simp) v (by simpa only [StageSplit.rest_vertices] using hv))
    (fun R hR => ⟨advance_nonempty H.system (i+1) 200 [(H.system i Q).rest B] (by simpa using hrest) R hR,
      H.gap_order hn i hik hQ hB hR⟩)
    ((H.bounded i hi Q hQ).2.2.2.1 B hB) ((H.bounded i hi Q hQ).2.2.1 B hB)
    (H.local_mass_two hn (fun j hj => (hready j hj).log_large) i 200 hik hQ hB)
    P.vertices.card C t hC ht (Finset.card_le_card (H.box_subset i hQ hB)) hsmall ih ihq

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Real

lemma main_gap_scalar (q n S M L Nt Ni C t w : ℝ)
    (hn : 0 ≤ n) (hS : 0 ≤ S) (hC : 0 ≤ C) (ht : 0 ≤ t) (hw : 0 < w)
    (hM : M ≤ mainP*S) (hL : L ≤ mainH*n/w)
    (hNt : Nt ≤ n+mainH*n/w) (hNilo : n ≤ Ni) (hNihi : Ni ≤ 2*n)
    (hq : q ≤ L+(9+C*mainEta)*M+(t+8)*Nt+(8-t/3)*S+((2/3)*t/w-8)*Ni) :
    q ≤ mainA₂*(S+n/w)+(C/100)*S+t*(n-S/3+mainA₁*n/w) := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hT := mul_le_mul_of_nonneg_left hNt (by linarith : 0 ≤ t+8)
  have hI := mul_le_mul_of_nonneg_left hNihi (by positivity : 0 ≤ (2/3)*t/w)
  have hI' : -8*Ni ≤ -8*n := by linarith
  have hA := mul_le_mul_of_nonneg_right (le_max_left (9*mainP+8) (9*mainH)) hS
  have hB := mul_le_mul_of_nonneg_right (le_max_right (9*mainP+8) (9*mainH)) (div_nonneg hn hw.le)
  change (9*mainP+8)*S ≤ mainA₂*S at hA
  change 9*mainH*(n/w) ≤ mainA₂*(n/w) at hB
  simp only [mainEta,mainP,mainA₁,div_eq_mul_inv] at hc hT hI hI' hA hB hq hL ⊢
  nlinarith only [hc,hT,hI,hI',hA,hB,hq,hL]

lemma main_terminal_scalar (q n M C Dstar : ℝ) (hn : 0 ≤ n) (hC : 0 ≤ C)
    (hCbig : 4*(20+Dstar+18*mainP) ≤ C) (hM : M ≤ 2*mainP*n)
    (hq : q ≤ (20+Dstar)*n+(9+C*mainEta)*M) :
    q ≤ C*Batch.inductionPhi n*n := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hbig := mul_le_mul_of_nonneg_right hCbig hn
  have hphi := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds n).1 (mul_nonneg hC hn)
  have hCn : 0 ≤ C*n := mul_nonneg hC hn
  simp only [mainEta,mainP] at hc hbig hq
  nlinarith only [hq,hc,hbig,hphi,hCn]

end
end ErdosGallai

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

lemma Layers.gap_log (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i) :
    logb 2 (H.scale (i+200)) = scaleTheta^200 * logb 2 (H.scale i) := by
  dsimp only [Layers.scale]
  rw [inductionScale_add _ (by positivity)]
  exact Real.logb_rpow_eq_mul_logb_of_pos (inductionScale_pos _ (by linarith) _)

lemma Layers.gap_mass (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (i)
    (hik : i+200 < H.count) :
    H.mass (i+201) ≤ (P.vertices.card:ℝ) + ErdosGallai.mainH*P.vertices.card/logb 2 (H.scale i) := by
  have hh := H.mass_upper hn (fun j hj => (hready j hj).log_large) (i+200) hik
  rw [H.gap_log hn] at hh
  convert hh using 1 ; try omega
  unfold ErdosGallai.mainH
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma Layers.gap_cycles (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (i)
    (hik : i+200 < H.count) :
    ((pastCycles H.system 0 (i+201) [P]).length:ℝ) ≤
      ErdosGallai.mainH*P.vertices.card/logb 2 (H.scale i) := by
  have hh := H.cycles_bound hn hready (i+200) hik
  rw [H.gap_log hn] at hh
  have hw : 0 < logb 2 (H.scale i) := inductionScale_log_pos _ hn i
  calc
    _ ≤ 20*P.vertices.card/(scaleTheta^200*logb 2 (H.scale i)) := hh
    _ ≤ 80*P.vertices.card/(scaleTheta^200*logb 2 (H.scale i)) :=
      div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)]) (by positivity)
    _ = _ := by unfold ErdosGallai.mainH; simp only [div_eq_mul_inv,mul_inv_rev]; ring

lemma Layers.boundary_cost (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) :
    costMass (H.frontier H.count) ≤ Dstar*P.vertices.card := by
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  have hD : 0 ≤ Dstar := by
    have hh := H.last_lt
    have hd := inductionScale_pos P.vertices.card (by linarith) H.count
    linarith
  have hcost : ∀ Q ∈ H.frontier H.count, (decompositionCost Q.graph:ℝ) ≤ (Dstar/2)*Q.vertices.card := by
    intro Q hQ
    have hQne := advance_nonempty H.system 0 H.count [P] (by simpa using hne) Q hQ
    have hc : (0:ℝ) < Q.vertices.card := by exact_mod_cast Finset.card_pos.mpr hQne
    have hg := (div_le_iff₀ hc).mp (H.degree H.count le_rfl Q hQ)
    have hh := mul_le_mul_of_nonneg_right H.last_lt.le hc.le
    have he := (Nat.cast_le.mpr (decompositionCost_edgeCount Q.graph) : (_:ℝ) ≤ _)
    nlinarith only [hg,hh,he]
  have hh := piece_list_cost (H.frontier H.count) (Dstar/2) hcost
  have hm := mul_le_mul_of_nonneg_left (H.mass_two hn (fun j hj => (hready j hj).log_large) H.count le_rfl)
    (div_nonneg hD (by norm_num : (0:ℝ) ≤ 2))
  change costMass (H.frontier H.count) ≤ (Dstar/2)*H.mass H.count at hh
  nlinarith only [hh,hm]

lemma Layers.terminal_cost (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (c : ℝ)
    (hp : ∀ R ∈ pastPieces H.system 0 H.count [P], (decompositionCost R.graph:ℝ) ≤ c*R.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ (20+Dstar)*P.vertices.card + c*vertexMass (pastPieces H.system 0 H.count [P]) := by
  have hcost := past_cost H.system 0 H.count P c hp
  have he := H.boundary_cost hn hready
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt H.positive)
  have hcy := H.cycles_bound hn hready j (by omega)
  have hw := (hready j (by omega)).log_large
  have hdiv : 20*(P.vertices.card:ℝ)/logb 2 (H.scale j) ≤ 20*P.vertices.card :=
    div_le_self (by positivity) (by linarith)
  rw [hj] at hcost he ⊢
  nlinarith only [hcost,he,hcy,hdiv]

end
end ErdosGallai.Scale

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

lemma Layers.pieceSequence_nonneg (H : Layers P Dstar) (j) : 0 ≤ H.pieceSequence j := by
  unfold Layers.pieceSequence
  split_ifs
  · exact vertexMass_nonneg _
  · rfl

lemma Layers.pieceSequence_zero (H : Layers P Dstar) (j) (hj : H.count ≤ j) :
    H.pieceSequence j = 0 := by simp only [Layers.pieceSequence,ite_eq_right (by omega : ¬ j < H.count)]

lemma Layers.past_mass_eq_sequence (H : Layers P Dstar) (k) (hk : k ≤ H.count) :
    vertexMass (pastPieces H.system 0 k [P]) = ∑ j ∈ range k, H.pieceSequence j := by
  rw [pastPieces_mass]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.zero_add,Layers.pieceSequence,ite_eq_left (by have := Finset.mem_range.mp hj; omega : j < H.count)]

lemma Layers.prefix_choice (H : Layers P Dstar) :
    vertexMass (pastPieces H.system 0 H.count [P]) = 0 ∨
    ∃ i < H.count, 0 < H.pieceMass i ∧
      ∀ k ≤ H.count, k ≤ i+201 →
        vertexMass (pastPieces H.system 0 k [P]) ≤ ErdosGallai.mainP*H.pieceMass i := by
  by_cases he : ∃ j, 0 < H.pieceSequence j
  · right
    obtain ⟨i,hi,hpref⟩ := ErdosGallai.prefix_selection H.pieceSequence H.pieceSequence_nonneg
      200 H.count H.pieceSequence_zero he
    have hic : i < H.count := by
      by_contra hi'
      rw [H.pieceSequence_zero i (by omega)] at hi
      linarith
    simp only [Layers.pieceSequence,ite_eq_left hic] at hi
    refine ⟨i,hic,hi,?_⟩
    intro k hk hki
    rw [H.past_mass_eq_sequence k hk]
    have hh : (∑ j ∈ range k, H.pieceSequence j) ≤ ∑ j ∈ range (i+200+1), H.pieceSequence j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => H.pieceSequence_nonneg j)
    apply hh.trans
    norm_num only [Layers.pieceSequence,ite_eq_left hic,ErdosGallai.mainP,Nat.cast_ofNat] at hpref ⊢
    exact hpref
  · left
    rw [H.past_mass_eq_sequence H.count le_rfl]
    apply Finset.sum_eq_zero
    intro j _
    exact le_antisymm (le_of_not_gt (fun h => he ⟨j,h⟩)) (H.pieceSequence_nonneg j)

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

lemma main_edge_bound {V : Type} [Fintype V] (G : SimpleGraph V) :
    2*(Scale.edgeCount G:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
  classical
  have h : (G.edgeFinset.card:ℝ) ≤ ((Fintype.card V).choose 2:ℝ) :=
    Nat.cast_le.mpr G.card_edgeFinset_le_card_choose_two
  rw [Nat.cast_choose_two] at h
  change 2*(G.edgeFinset.card:ℝ) ≤ _
  nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)]

lemma main_cost_eq_scale {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Scale.decompositionCost G := by rfl
lemma main_cost_eq_batch {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Batch.decompositionCost G := by rfl

theorem main_cost_bound : ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
  classical
  let wmin : ℝ := max 80 (((mainA₁+1)/Batch.inductionDelta)^2)
  obtain ⟨Da,ha,hLayers⟩ := Scale.uniform_layers
  obtain ⟨Db,hb,hPiece⟩ := Scale.uniform_committed_piece_cost
  obtain ⟨Dc,hc,hGap⟩ := Scale.uniform_gap_prefix_cost
  obtain ⟨Dr,hr,hReady⟩ := main_scale_ready_cutoff wmin
  let Dstar : ℝ := max (max Da Db) (max Dc Dr)
  have hDa : Da ≤ Dstar := (le_max_left Da Db).trans (le_max_left _ _)
  have hDb : Db ≤ Dstar := (le_max_right Da Db).trans (le_max_left _ _)
  have hDc : Dc ≤ Dstar := (le_max_left Dc Dr).trans (le_max_right _ _)
  have hDr : Dr ≤ Dstar := (le_max_right Dc Dr).trans (le_max_right _ _)
  have hDstar : 1 < Dstar := ha.trans_le hDa
  let C : ℝ := max (4*(20+Dstar+18*mainP)) (7*mainA₂)
  have hCbig : 4*(20+Dstar+18*mainP) ≤ C := le_max_left _ _
  have hCA : 7*mainA₂ ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith [mainP_pos]) hCbig
  have hC : 0 ≤ C := hCpos.le
  refine ⟨C,hCpos,?_⟩
  have hmain : ∀ n : ℕ, ∀ (V : Type) [Fintype V], Fintype.card V = n → ∀ (G : SimpleGraph V),
      (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ hn G
      subst n
      have hn0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      by_cases hsmall : (Fintype.card V:ℝ) < Dstar
      · have he := main_edge_bound G
        have hq : (decompositionCost G:ℝ) ≤ Scale.edgeCount G :=
          Nat.cast_le.mpr (Scale.decompositionCost_edgeCount G)
        have hnD := mul_le_mul_of_nonneg_right hsmall.le hn0
        have hphi := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds (Fintype.card V)).1
          (mul_nonneg hC hn0)
        have hbig := mul_le_mul_of_nonneg_right hCbig hn0
        have hP := mul_nonneg mainP_pos.le hn0
        nlinarith only [he,hq,hnD,hphi,hbig,hP]
      · have hnD : Dstar ≤ (Fintype.card V:ℝ) := le_of_not_gt hsmall
        have hn1 : 1 < (Fintype.card V:ℝ) := hDstar.trans_le hnD
        let P : Scale.AssignedPiece V := ⟨univ,G,fun _ _ _ => ⟨mem_univ _,mem_univ _⟩⟩
        have hpc : P.vertices.card = Fintype.card V := Finset.card_univ
        have hp1 : 1 < (P.vertices.card:ℝ) := by simpa only [hpc] using hn1
        have hdeg : 2*(Scale.edgeCount P.graph:ℝ)/P.vertices.card ≤ P.vertices.card := by
          apply (div_le_iff₀ (by linarith : (0:ℝ) < P.vertices.card)).mpr
          simpa only [hpc,P,pow_two] using main_edge_bound G
        obtain ⟨H⟩ := hLayers Dstar hDa V P (by simpa only [hpc] using hnD) hdeg
        have hready' : ∀ j < H.count, MainScaleReady wmin (H.scale j) := by
          intro j hj
          exact hReady _ (hDr.trans (H.cutoff j hj))
        have hready : ∀ j < H.count, MainScaleReady 80 (H.scale j) := by
          intro j hj
          have hh := hready' j hj
          exact ⟨hh.gt_one,(le_max_left _ _).trans hh.log_large,hh.cycle_power,hh.batch_power,
            hh.bad_power,hh.skip_power,hh.active_eight⟩
        have ihw : ∀ (Q : Type) [Fintype Q] (F : SimpleGraph Q), Fintype.card Q < P.vertices.card →
            (decompositionCost F:ℝ) ≤ C*Fintype.card Q := by
          intro Q _ F hQ
          have hh := ih (Fintype.card Q) (by simpa only [hpc] using hQ) Q rfl F
          have hp := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds (Fintype.card Q)).2
            (mul_nonneg hC (Nat.cast_nonneg (Fintype.card Q) : (0:ℝ) ≤ _))
          nlinarith only [hh,hp]
        have hpieces := hPiece Dstar hDb V P H C hC ihw
        have terminal (hm : Scale.vertexMass (Scale.pastPieces H.system 0 H.count [P]) ≤
            2*mainP*P.vertices.card) :
            (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
          have hh := H.terminal_cost hp1 hready (9+C*mainEta) (hpieces H.count le_rfl)
          have ht := main_terminal_scalar _ P.vertices.card _ C Dstar (Nat.cast_nonneg _) hC hCbig hm hh
          simpa only [hpc,P,← main_cost_eq_scale] using ht
        rcases H.prefix_choice with hz | ⟨i,hic,hi,hprefix⟩
        · apply terminal
          rw [hz]
          exact mul_nonneg (mul_nonneg (by norm_num) mainP_pos.le) (Nat.cast_nonneg _)
        · by_cases hgap : i+200 < H.count
          · let t := C*Batch.inductionPhi ((H.scale i)^(3/10:ℝ))
            have ht : 0 ≤ t := mul_nonneg hC (by linarith [(Batch.inductionPhi_bounds ((H.scale i)^(3/10:ℝ))).1])
            have ihq : ∀ (Q : Type) [Fintype Q] (F : SimpleGraph Q), Fintype.card Q < P.vertices.card →
                (Fintype.card Q:ℝ) ≤ (H.scale i)^(3/10:ℝ) →
                (Batch.decompositionCost F:ℝ) ≤ t*Fintype.card Q := by
              intro Q _ F hQ hQD
              have hh := ih (Fintype.card Q) (by simpa only [hpc] using hQ) Q rfl F
              by_cases h0 : Fintype.card Q = 0
              · simpa only [h0,Nat.cast_zero,mul_zero,← main_cost_eq_batch] using hh
              · have h1 : (1:ℝ) ≤ Fintype.card Q := by exact_mod_cast (by omega : 1 ≤ Fintype.card Q)
                have hp := Batch.inductionPhi_monotone h1 (h1.trans hQD) hQD
                have hp' := mul_le_mul_of_nonneg_left hp
                  (mul_nonneg hC (Nat.cast_nonneg (Fintype.card Q) : (0:ℝ) ≤ _))
                change (decompositionCost F:ℝ) ≤ C*Batch.inductionPhi ((H.scale i)^(3/10:ℝ))*Fintype.card Q
                nlinarith only [hh,hp']
            have hlocal := hGap Dstar hDc V P H hp1 hready i hgap C t hC ht ihw ihq
              (hpieces (i+201) (by omega))
            have hscalar := main_gap_scalar _ P.vertices.card (H.pieceMass i)
              (Scale.vertexMass (Scale.pastPieces H.system 0 (i+201) [P]))
              ((Scale.pastCycles H.system 0 (i+201) [P]).length:ℝ)
              (H.mass (i+201)) (H.mass (i+1)) C t (logb 2 (H.scale i))
              (Nat.cast_nonneg _) (Scale.vertexMass_nonneg _) hC ht
              (by linarith [(hready i hic).log_large])
              (hprefix (i+201) (by omega) le_rfl) (H.gap_cycles hp1 hready i hgap)
              (H.gap_mass hp1 hready i hgap) (H.mass_lower (i+1))
              (H.mass_two hp1 (fun j hj => (hready j hj).log_large) (i+1) (by omega)) hlocal
            have habs := Batch.induction_cost_absorbed (H.scale i) P.vertices.card (H.pieceMass i)
              C mainA₁ mainA₂ (hready i hic).gt_one (Scale.inductionScale_le _ hp1.le i)
              (Scale.vertexMass_nonneg _) hC mainA₁_nonneg mainA₂_nonneg hCA
              (by linarith [(hready i hic).log_large])
              ((le_max_right _ _).trans (hready' i hic).log_large)
            have hfinal := hscalar.trans habs
            simpa only [hpc,P,← main_cost_eq_scale] using hfinal
          · apply terminal
            calc
              _ ≤ mainP*H.pieceMass i := hprefix H.count le_rfl (by omega)
              _ ≤ mainP*(2*P.vertices.card) := mul_le_mul_of_nonneg_left
                (H.pieceMass_two hp1 (fun j hj => (hready j hj).log_large) i hic) mainP_pos.le
              _ = _ := by ring
  intro V _ G
  exact hmain (Fintype.card V) V rfl G

theorem erdos_gallai_oai : MainStatement := by
  obtain ⟨C,hC,hcost⟩ := main_cost_bound
  refine ⟨C,hC,?_⟩
  intro n G
  refine ⟨decompositionCost G,decompositionCost_spec G,?_⟩
  have hh := hcost (Fin n) G
  simp only [Fintype.card_fin] at hh
  have hp := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds n).2
    (mul_nonneg hC.le (Nat.cast_nonneg n : (0:ℝ) ≤ _))
  nlinarith only [hh,hp]

end
end ErdosGallai

end

end
end

end OAI
end

theorem solution : type_of% @OAI.ErdosGallai.erdos_gallai_oai := @OAI.ErdosGallai.erdos_gallai_oai
