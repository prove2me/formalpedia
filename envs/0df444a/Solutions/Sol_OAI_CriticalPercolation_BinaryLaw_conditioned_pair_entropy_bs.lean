-- Prove2me | solution 1 for OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:10:00.327545+00:00
-- url     : https://prove2.me/submissions/2832936c-cb2c-466e-8821-1e549b0621b3

import Mathlib
import Definitions.Def_OAIQ078B002

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_EndpointKernel
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.FiniteEntropy

lemma integral_polynomial_sum (n : ℕ) (c : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, ∑ i ∈ Finset.range n, c i * t^i) =
      ∑ i ∈ Finset.range n, c i / ((i:ℝ)+1) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  · intro i hi
    exact (by fun_prop : Continuous (fun t : ℝ => c i * t^i)).intervalIntegrable 0 1

lemma integral_cubic_square (a b c d : ℝ) :
    (∫ t in (0:ℝ)..1, (a + b*t + c*t^2 + d*t^3)^2) =
      a^2 + a*b + (b^2+2*a*c)/3 + (2*a*d+2*b*c)/4 +
        (c^2+2*b*d)/5 + (2*c*d)/6 + d^2/7 := by
  have hpoly (t : ℝ) : (a+b*t+c*t^2+d*t^3)^2 =
      ∑ i ∈ Finset.range 7, (![a^2, 2*a*b, b^2+2*a*c, 2*a*d+2*b*c,
        c^2+2*b*d, 2*c*d, d^2] : Fin 7 → ℝ) ⟨i % 7, Nat.mod_lt _ (by norm_num)⟩ * t^i := by
    simp [Finset.sum_range_succ]
    ring
  simp_rw [hpoly]
  rw [integral_polynomial_sum]
  simp [Finset.sum_range_succ]
  ring

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy

lemma continuous_endpointKernel : Continuous endpointKernel := by
  unfold endpointKernel
  fun_prop

lemma integral_endpointKernel_sq :
    (∫ t in (0:ℝ)..1, (endpointKernel t)^2) = 16 := by
  have he (t : ℝ) : endpointKernel t = 16 + (-120)*t + 240*t^2 + (-140)*t^3 := by
    unfold endpointKernel; ring
  simp_rw [he]
  rw [integral_cubic_square]
  norm_num

lemma integral_endpointKernel_power {k : ℕ} (hk : k ≤ 3) :
    (∫ t in (0:ℝ)..1, endpointKernel t * (1-t)^k) = 1 := by
  interval_cases k
  · let c : Fin 7 → ℝ := ![16, -120, 240, -140, 0, 0, 0]
    have ht (t : ℝ) : endpointKernel t * (1-t)^0 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]
  · let c : Fin 7 → ℝ := ![16, -136, 360, -380, 140, 0, 0]
    have ht (t : ℝ) : endpointKernel t * (1-t)^1 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]
  · let c : Fin 7 → ℝ := ![16, -152, 496, -740, 520, -140, 0]
    have ht (t : ℝ) : endpointKernel t * (1-t)^2 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]
  · let c : Fin 7 → ℝ := ![16, -168, 648, -1236, 1260, -660, 140]
    have ht (t : ℝ) : endpointKernel t * (1-t)^3 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Uniform01
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instNullSingletonClassRealUniform01 _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma split_symm_apply (i j : I) (u : ℝ × ({j : I // j ≠ i} → ℝ)) :
    (split i).symm u j = if h : j = i then u.1 else u.2 ⟨j,h⟩ := by
  simp only [split, MeasurableEquiv.symm_mk, Equiv.funSplitAt, Equiv.piSplitAt,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk]
  split_ifs with h
  · subst j; rfl
  · rfl

lemma split_preserving (i : I) : MeasurePreserving (split i) law
    (uniform01.prod (law (I := {j : I // j ≠ i}))) := by
  apply MeasurePreserving.symm (split i).symm
  refine ⟨(split i).symm.measurable, ?_⟩
  unfold law
  refine (Measure.pi_eq fun s _ => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have he : (split i).symm ⁻¹' (Set.univ.pi s) =
      s i ×ˢ (Set.univ.pi fun j : {j : I // j ≠ i} => s j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h
      constructor
      · simpa [split_symm_apply] using h i
      · intro j; simpa [split_symm_apply, j.property] using h j
    · rintro ⟨h₁,h₂⟩ j
      by_cases h : j = i
      · subst j; simpa [split_symm_apply] using h₁
      · simpa [split_symm_apply, h] using h₂ ⟨j,h⟩
  rw [he, Measure.prod_prod, Measure.pi_pi]
  have hprod := Fintype.prod_subtype_mul_prod_subtype (fun j : I => j = i)
    (fun j => uniform01 (s j))
  simpa only [Fintype.prod_unique, (default : {j : I // j = i}).property] using hprod

lemma uniform01_Ioi {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    uniform01 (Ioi t) = ENNReal.ofReal (1-t) := by
  rw [uniform01, Measure.restrict_apply measurableSet_Ioi]
  have he : Ioi t ∩ Icc (0:ℝ) 1 = Ioc t 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · intro h; exact ⟨h.1,h.2.2⟩
    · intro h; exact ⟨h.1, ht.1.trans h.1.le, h.2⟩
  rw [he, Real.volume_Ioc]

lemma integral_survival (S : Finset I) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (∫ u : I → ℝ, if ∀ j ∈ S, t < u j then (1:ℝ) else 0 ∂law) = (1-t)^S.card := by
  have he : {u : I → ℝ | ∀ j ∈ S, t < u j} =
      Set.univ.pi (fun j => if j ∈ S then Ioi t else Set.univ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h j; split_ifs with hj
      · exact h j hj
      · trivial
    · intro h j hj; simpa [hj] using h j
  have hf : (fun u : I → ℝ => if ∀ j ∈ S, t < u j then (1:ℝ) else 0) =
      ({u : I → ℝ | ∀ j ∈ S, t < u j}).indicator (fun _ => (1:ℝ)) := by
    funext u
    simp [Set.indicator]
  rw [hf]
  rw [integral_indicator]
  · rw [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
      he, law, Measure.pi_pi]
    simp only [apply_ite, uniform01_Ioi ht, measure_univ, ENNReal.toReal_prod,
      apply_ite, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2), ENNReal.toReal_one]
    rw [Finset.prod_ite_mem Finset.univ S (fun _ => 1-t)]
    simp
  · rw [he]
    exact MeasurableSet.univ_pi fun j => by split_ifs <;> measurability

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_FreshSet
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instNullSingletonClassRealUniform01 _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma measurableSet_freshSet (i : I) (S : Finset {j : I // j ≠ i}) :
    MeasurableSet (freshSet i S) := by
  have he : freshSet i S = ⋂ j ∈ (S : Set {j : I // j ≠ i}),
        {u : I → ℝ | u i < u j.val} := by
    ext u
    simp [freshSet]
  rw [he]
  exact MeasurableSet.biInter S.finite_toSet.countable fun j _ =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j.val)

lemma integrable_eval_continuous (f : ℝ → ℝ) (hf : Continuous f) (i : I) :
    Integrable (fun u : I → ℝ => f (u i)) law := by
  apply integrable_comp_eval
  exact hf.integrableOn_Icc

lemma integral_freshSet (f : ℝ → ℝ) (hf : Continuous f) (i : I)
    (S : Finset {j : I // j ≠ i}) :
    (∫ u in freshSet i S, f (u i) ∂law) =
      ∫ t, f t * (1-t)^S.card ∂uniform01 := by
  let F : (I → ℝ) → ℝ := (freshSet i S).indicator (fun u => f (u i))
  have hF : Integrable F law :=
    (integrable_eval_continuous f hf i).indicator (measurableSet_freshSet i S)
  rw [← integral_indicator (measurableSet_freshSet i S)]
  change (∫ u, F u ∂law) = _
  rw [← (split_preserving i).symm.integral_comp' F]
  have hi : Integrable (F ∘ (split i).symm)
      (uniform01.prod (law (I := {j : I // j ≠ i}))) :=
    (split_preserving i).symm.integrable_comp_of_integrable hF
  rw [integral_prod (fun x => F ((split i).symm x)) (by simpa [Function.comp_def] using hi)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have he (u : {j : I // j ≠ i} → ℝ) : F ((split i).symm (t,u)) =
      f t * (if ∀ j ∈ S, t < u j then (1:ℝ) else 0) := by
    dsimp [F]
    simp only [Set.indicator_apply, freshSet, Set.mem_ofPred_eq, split_symm_apply,
      ↓reduceDIte]
    split_ifs <;> simp_all
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  convert integral_survival S ht using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with u
  split_ifs <;> rfl

lemma uniform01_integral_eq_interval (f : ℝ → ℝ) :
    (∫ t, f t ∂uniform01) = ∫ t in (0:ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [uniform01, integral_Icc_eq_integral_Ioc]

open FiniteEntropy in

lemma weighted_fresh_identity (i : I) (S : Finset {j : I // j ≠ i}) (hS : S.card ≤ 3) :
    (∫ u in freshSet i S, endpointKernel (u i) ∂law) = 1 := by
  rw [integral_freshSet _ continuous_endpointKernel, uniform01_integral_eq_interval]
  exact integral_endpointKernel_power hS

open FiniteEntropy in

lemma square_weight_integral (i : I) :
    (∫ u : I → ℝ, (endpointKernel (u i))^2 ∂law) = 16 := by
  rw [show law (I := I) = Measure.pi (fun _ : I => uniform01) from rfl,
    integral_comp_eval (μ := fun _ : I => uniform01) (i := i)
      (f := fun t => (endpointKernel t)^2) (continuous_endpointKernel.pow 2).aestronglyMeasurable,
    uniform01_integral_eq_interval]
  exact integral_endpointKernel_sq

end CriticalPercolation.Priority

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma measurableSet_pairwise (l : List I) :
    MeasurableSet {u : I → ℝ | l.Pairwise fun i j => u i < u j} := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hc : {u : I → ℝ | (i::l).Pairwise fun a b => u a < u b} =
        {u : I → ℝ | ∀ j ∈ l, u i < u j} ∩
          {u : I → ℝ | l.Pairwise fun a b => u a < u b} := by
      ext u; exact List.pairwise_cons
    rw [hc]
    apply MeasurableSet.inter _ ih
    have he : {u : I → ℝ | ∀ j ∈ l, u i < u j} =
        ⋂ j ∈ (l.toFinset : Set I), {u : I → ℝ | u i < u j} := by
      ext u
      simp
    rw [he]
    exact MeasurableSet.biInter l.toFinset.finite_toSet.countable fun (j : I) _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

lemma measurableSet_cell (o : Order I) : MeasurableSet (cell o) :=
  measurableSet_pairwise o.val

lemma exists_cell (u : I → ℝ) (hu : Function.Injective u) : ∃ o : Order I, u ∈ cell o := by
  let r : I → I → Prop := fun i j => u i ≤ u j
  let : Std.Total r := ⟨fun i j => le_total (u i) (u j)⟩
  let : IsTrans I r := ⟨fun _ _ _ => le_trans⟩
  let l := (enumeration (I := I)).insertionSort r
  have hperm : l.Perm enumeration := List.perm_insertionSort r _
  refine ⟨⟨l,hperm⟩, ?_⟩
  have hp : l.Pairwise r := List.pairwise_insertionSort r _
  have hn : l.Pairwise (fun a b => a ≠ b) :=
    hperm.nodup_iff.mpr (Finset.nodup_toList _)
  have hh : l.Pairwise (fun a b => r a b ∧ a ≠ b) := hp.and hn
  exact hh.imp fun {i j} hij => lt_of_le_of_ne hij.1 (fun he => hij.2 (hu he))

lemma cell_disjoint {o o' : Order I} (h : o ≠ o') : Disjoint (cell o) (cell o') := by
  apply Set.disjoint_left.mpr
  intro u hu hu'
  apply h
  apply Subtype.ext
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => False.elim (lt_asymm hab hba))
    hu hu' (o.property.trans o'.property.symm)

lemma before_iff (u : I → ℝ) (o : Order I) (hu : u ∈ cell o) {pre post : List I}
    {i j : I} (he : o.val = pre++i::post) (hji : j ≠ i) :
    j ∈ pre ↔ u j < u i := by
  rw [cell, Set.mem_ofPred_eq, he, List.pairwise_append, List.pairwise_cons] at hu
  constructor
  · intro hj
    exact hu.2.2 j hj i (by simp)
  · intro hj
    have hm := mem_order o j
    rw [he, List.mem_append, List.mem_cons] at hm
    rcases hm with hp | h | ht
    · exact hp
    · exact False.elim (hji h)
    · exact False.elim (lt_asymm hj (hu.2.1.1 j ht))

end CriticalPercolation.Priority

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_AeEvalNe
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

lemma ae_eval_ne (i j : I) (hji : j ≠ i) :
    ∀ᵐ u : I → ℝ ∂law, u i ≠ u j := by
  have hj : ∀ t : ℝ, ∀ᵐ v : {k : I // k ≠ i} → ℝ ∂law,
      t ≠ v ⟨j,hji⟩ := by
    intro t
    apply ae_iff.mpr
    have hz := Measure.pi_eval_preimage_null
      (fun _ : {k : I // k ≠ i} => uniform01)
      (i := ⟨j,hji⟩) (measure_singleton t)
    have he : {v : {k : I // k ≠ i} → ℝ | ¬t ≠ v ⟨j,hji⟩} =
        (Function.eval ⟨j,hji⟩ : ({k : I // k ≠ i} → ℝ) → ℝ) ⁻¹' {t} := by
      ext v
      simp [eq_comm]
    change law {v : {k : I // k ≠ i} → ℝ | ¬t ≠ v ⟨j,hji⟩} = 0
    rw [he]
    exact hz
  have hp : ∀ᵐ z : ℝ × ({k : I // k ≠ i} → ℝ)
      ∂uniform01.prod law, z.1 ≠ z.2 ⟨j,hji⟩ := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    exact Filter.Eventually.of_forall hj
  exact (split_preserving i).quasiMeasurePreserving.ae hp

lemma ae_injective : ∀ᵐ u : I → ℝ ∂law, Function.Injective u := by
  have h : ∀ i j : I, ∀ᵐ u : I → ℝ ∂law, u i = u j → i = j := by
    intro i j
    by_cases hji : j = i
    · subst j; exact Filter.Eventually.of_forall (fun _ _ => rfl)
    · filter_upwards [ae_eval_ne i j hji] with u hu
      exact fun he => False.elim (hu he)
  change ∀ᵐ u : I → ℝ ∂law, ∀ i j, u i = u j → i = j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  exact h i

lemma ae_exists_cell : ∀ᵐ u : I → ℝ ∂law, ∃ o : Order I, u ∈ cell o := by
  filter_upwards [ae_injective] with u hu
  exact exists_cell u hu

lemma sum_cell_indicator (f : (I → ℝ) → ℝ) :
    (fun u => ∑ o : Order I, (cell o).indicator f u) =ᵐ[law] f := by
  filter_upwards [ae_exists_cell] with u hu
  obtain ⟨o,ho⟩ := hu
  rw [Finset.sum_eq_single o]
  · exact Set.indicator_of_mem ho f
  · intro b _ hb
    apply Set.indicator_of_notMem
    exact fun hub => Set.disjoint_left.mp (cell_disjoint hb) hub ho
  · simp

lemma sum_integral_cells (f : (I → ℝ) → ℝ) (hf : Integrable f law) :
    (∑ o : Order I, ∫ u in cell o, f u ∂law) = ∫ u, f u ∂law := by
  simp_rw [← integral_indicator (measurableSet_cell _)]
  rw [← integral_finsetSum]
  · exact integral_congr_ae (sum_cell_indicator f)
  · intro o _
    exact hf.indicator (measurableSet_cell o)

end CriticalPercolation.Priority

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchTree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

namespace LazyDFS
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

lemma compile_valid (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) :
    (compile G order B fuel st stack).Valid st.read := by
  induction fuel generalizing st stack with
  | zero => trivial
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · trivial
    · cases stack with
      | nil => trivial
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest
        · exact ⟨fun he => hd (Or.inr (Or.inl he)), ih _ _, ih _ _⟩

end LazyDFS
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)

omit [Fintype A] in
lemma density_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P] (ω : E → A) :
    density w ω =
      density (fun e : {e // P e} => w e) (fun e => ω e) *
      density (fun e : {e // ¬ P e} => w e) (fun e => ω e) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun e => w e (ω e))).symm

lemma expect_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : (E → A) → ℝ) :
    expect w f =
      expect (fun e : {e // P e} => w e) (fun a =>
        expect (fun e : {e // ¬ P e} => w e) (fun b =>
          f ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b)))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => A)
  unfold expect
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have h₁ : (fun i : {e // P e} => e.symm (a, b) i) = a :=
    congrArg Prod.fst (e.apply_symm_apply (a, b))
  have h₂ : (fun i : {e // ¬ P e} => e.symm (a, b) i) = b :=
    congrArg Prod.snd (e.apply_symm_apply (a, b))
  rw [density_split w P, h₁, h₂, mul_assoc]

lemma expect_factor (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : ({e // P e} → A) → ℝ) (g : ({e // ¬ P e} → A) → ℝ) :
    expect w (fun ω => f (fun e => ω e) * g (fun e => ω e)) =
      expect (fun e : {e // P e} => w e) f *
        expect (fun e : {e // ¬ P e} => w e) g := by
  classical
  rw [expect_split w P]
  have h₁ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = a := by
    intro a b
    exact congrArg Prod.fst ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  have h₂ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // ¬ P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = b := by
    intro a b
    exact congrArg Prod.snd ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  simp_rw [h₁, h₂]
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  ring

lemma expect_indep (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (S : Set E) {f g : (E → A) → ℝ}
    (hf : DependsOn f S) (hg : DependsOn g Sᶜ) :
    expect w (fun ω => f ω * g ω) = expect w f * expect w g := by
  classical
  obtain ⟨f', rfl⟩ := dependsOn_iff_exists_comp.mp hf
  obtain ⟨g', rfl⟩ := dependsOn_iff_exists_comp.mp hg
  have hw₁ : ∀ e : S, ∑ a, w e a = 1 := fun e => hw e
  have hw₂ : ∀ e : {e // e ∉ S}, ∑ a, w e a = 1 := fun e => hw e
  have hf' : expect w (fun ω => f' (fun e => ω e)) =
      expect (fun e : S => w e) f' := by
    have h := expect_factor w (fun e => e ∈ S) f' (fun _ => 1)
    simpa only [mul_one, expect_const _ hw₂] using h
  have hg' : expect w (fun ω => g' (fun e => ω e)) =
      expect (fun e : {e // e ∉ S} => w e) g' := by
    have h := expect_factor w (fun e => e ∈ S) (fun _ => 1) g'
    simp only [one_mul, expect_const _ hw₁] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  change expect w (fun ω => f' (fun e => ω e) * g' (fun e => ω e)) =
    expect w (fun ω => f' (fun e => ω e)) * expect w (fun ω => g' (fun e => ω e))
  rw [hf', hg']
  convert expect_factor w (fun e => e ∈ S) f' g' using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Distribution
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

lemma expect_nonneg {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect w f := by
  rw [← expect_zero w]
  exact expect_mono hw hf

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Prob
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b) (P : Set E → Prop) :
    0 ≤ prob w P := expect_nonneg hp (fun _ => by split_ifs <;> norm_num)

lemma prob_mono (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {P Q : Set E → Prop} (h : ∀ ω, P ω → Q ω) : prob w P ≤ prob w Q := by
  apply expect_mono hp
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
  exact (hQ (h ω hP)).elim

lemma prob_split (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w P = prob w (fun ω => P ω ∧ Q ω) + prob w (fun ω => P ω ∧ ¬Q ω) := by
  unfold prob
  rw [← expect_add]
  congr 1
  funext ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

lemma prob_congr (w : E → Prop → ℝ) {P Q : Set E → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : prob w P = prob w Q := by
  congr 1
  funext ω
  exact propext (h ω)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProbOr
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_diff (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w (fun ω => P ω ∧ ¬Q ω) = prob w P - prob w (fun ω => P ω ∧ Q ω) := by
  have hh := prob_split w P Q
  linarith
end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteProductPin
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype E] [Fintype A] in
lemma pin_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (e : E) (b : A) :
    ∀ j a, 0 ≤ pin w e b j a := by
  intro j a
  by_cases h : j = e
  · subst j; simp [pin]; split_ifs <;> norm_num
  · simpa [pin,h] using hw j a

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Delta
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_eval_indicator (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) : expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  classical
  have ht (ω : E → A) : density w ω * (if ω e = b then 1 else 0) =
      ∏ j, w j (ω j) * (if j = e then if ω j = b then 1 else 0 else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [density]
  simp only [expect, ht]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) : (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
      if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp
end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_coordinate_mask (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact expect_eval_indicator w hw e b

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_pin_eq_force (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (b : Prop) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect w (fun ω => f (Function.update ω e b)) := by
  apply mul_left_cancel₀ hb
  exact (expect_mask_pin w e b f).symm.trans (expect_coordinate_mask w hw e b f)

lemma expect_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect (pin w e a) (fun ω => f (Function.update ω e b)) := by
  rw [expect_pin_eq_force w hw e b hb,expect_pin_eq_force w hw e a ha]
  simp only [Function.update_idem]

lemma prob_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (P : Set E → Prop) :
    prob (pin w e b) P = prob (pin w e a) (fun ω => P (Function.update ω e b)) := by
  exact expect_pin_transport w hw e a b ha hb (fun ω => if P ω then 1 else 0)

lemma delta_eq_pivotal (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    delta w F e = prob (pin w e False)
      (fun ω => F (Function.update ω e True) ∧ ¬F ω) := by
  rw [delta,prob_pin_transport w hw e False True he0 he1]
  have hh := prob_diff (pin w e False)
    (fun ω => F (Function.update ω e True)) F
  have he : prob (pin w e False) (fun ω => F (Function.update ω e True) ∧ F ω) =
      prob (pin w e False) F := by
    apply prob_congr
    intro ω
    constructor
    · exact And.right
    · intro h
      refine ⟨hF _ _ ?_ h,h⟩
      intro j hj
      change Function.update (ω : Set E) e True j
      by_cases hje : j = e
      · subst j; erw [Function.update_self]; trivial
      · erw [Function.update_of_ne hje]; exact hj
  erw [he] at hh
  exact hh.symm

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Variance
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_true (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) :
    prob w (fun _ => True) = 1 := by
  simpa only [prob, if_true] using expect_const w hw 1

lemma prob_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : prob w F ≤ 1 := by
  exact (prob_mono w hn (fun _ _ => True.intro)).trans_eq (prob_true w hw)

lemma delta_unit (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    0 ≤ delta w F e ∧ delta w F e ≤ 1 := by
  rw [delta_eq_pivotal w hw e h0 h1 F hF]
  exact ⟨prob_nonneg _ (pin_nonneg w hn e False) _,
    prob_le_one _ (pin_normalized w hw e False) (pin_nonneg w hn e False) _⟩

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ForceClosed
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*}

variable [Fintype E]

omit [Fintype E] in
lemma homogeneous_normalized (w : E → Prop → ℝ) (p : ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e, ∑ b, w e b = 1 := by
  intro e
  simp [Fintype.univ_Prop,h0,h1]

omit [Fintype E] in
lemma homogeneous_positive (w : E → Prop → ℝ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e b, 0 < w e b := by
  intro e b
  by_cases hb : b
  · have : b = True := propext (iff_true_intro hb)
    rw [this,h1]; exact hp.1
  · have : b = False := propext (iff_false_intro hb)
    rw [this,h0]; exact sub_pos.mpr hp.2

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryDelta
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma queryDelta_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) : 0 ≤ T.queryDelta F w ω e := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
    have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
    simp only [queryDelta]
    split_ifs
    · exact (delta_unit w hw hn f hf0 hf1 F hF).1
    · exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
        (fresh_pin w p used hf f True)
    · exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
        (fresh_pin w p used hf f False)

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SequentialExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma contactWeight_nonneg (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Prop) (e : E) :
    0 ≤ G.contactWeight order B O a p w ω e := by
  unfold contactWeight
  split_ifs
  · apply mul_nonneg hp.1.le
    apply queryDelta_nonneg _ ∅ (LazyDFS.compile_valid G order B _ _ _) hp _ _ w
      (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
      (fun e _ => ⟨h0 e,h1 e⟩)
    rintro s t hst ⟨b,hb,hr⟩
    exact ⟨b,hb,hr.mono (G.openGraph_mono hst)⟩
  · exact le_rfl

lemma contactKernel_nonneg (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) :
    0 ≤ G.contactKernel order B a p w C ω mark := by
  unfold contactKernel
  by_cases ha : a ∈ C.1
  · rw [ite_eq_left ha]
    split_ifs <;> norm_num
  · rw [ite_eq_right ha]
    cases mark with
    | none => exact le_rfl
    | some e =>
      exact div_nonneg (G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e)
        (prob_nonneg w (fun e b => (homogeneous_positive w hp h0 h1 e b).le) _)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryLaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

universe uE

lemma anchors_length {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (anchors d x n h).length = n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [anchors,List.length_append,List.length_singleton,ih]

lemma firstIndex_spec {P : ℕ → Prop} (h : ∃ j, P j) : P (firstIndex P) := by
  rw [firstIndex,dite_eq_left h]
  exact Nat.find_spec h

lemma firstIndex_le {P : ℕ → Prop} {j : ℕ} (hj : P j) : firstIndex P ≤ j := by
  rw [firstIndex,dite_eq_left ⟨j,hj⟩]
  exact Nat.find_min' _ hj

variable {V E : Type*} (G : BondGraph V E)

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma density_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hr₀ : ∀ ω, 0 ≤ r₀ ω) (n : ℕ) (h : History E n)
    (ω : E → Prop) : 0 ≤ density G order d x p w r₀ n h ω := by
  induction n with
  | zero => exact hr₀ ω
  | succ n ih =>
    rw [density]
    split_ifs
    · exact mul_nonneg (ih h.1) (G.contactKernel_nonneg order _ _ hp w h0 h1 _ ω _)
    · exact le_rfl

end Density

section Seed
variable [Fintype V] [Fintype E]

lemma seed_nonneg (w : E → Prop → ℝ) (u v : V) (s : ℕ)
    (hδ : 0 < prob w (endpointEvent G u v s)) (ω : E → Prop) : 0 ≤ seed G w u v s ω := by
  unfold seed
  apply mul_nonneg (inv_nonneg.mpr hδ.le)
  split_ifs <;> norm_num

end Seed

section ExactLaw
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma kernel_parent_exists (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (a : V)
    (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order (anchorSet d x n h) a p w
      (G.clusterObject ω (anchorSet d x n h)) ω m ≠ 0) :
    ∃ j, parentPredicate G (anchors d x n h) a ω m j := by
  by_cases ha : a ∈ (G.clusterObject ω (anchorSet d x n h)).1
  · have hm : m=none := by
      by_contra hm
      simp only [contactKernel,ite_eq_left ha,ite_eq_right hm] at hk
      exact hk rfl
    subst m
    obtain ⟨v,⟨b,hb⟩,hr⟩ := ha
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
    exact ⟨j,(v,b),hj,hr.symm⟩
  · cases m with
    | none => simp only [contactKernel,ite_eq_right ha] at hk; exact (hk rfl).elim
    | some e =>
      have he : e ∈ G.cutEdges (G.clusterObject ω (anchorSet d x n h)).1 := by
        by_contra he
        simp only [contactKernel,ite_eq_right ha,contactWeight,ite_eq_right he,zero_div] at hk
        exact hk rfl
      obtain ⟨u,v,heq,-,z,⟨b,hb⟩,hr⟩ := he
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
      refine ⟨j,(z,b),hj,v,?_,hr⟩
      simp [heq]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma parent_lt_of_exists (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (h : ∃ j, parentPredicate G L a ω m j) : parent G L a ω m < L.length := by
  obtain ⟨z,hz,-⟩ := firstIndex_spec h
  exact (List.getElem?_eq_some_iff.mp hz).1

lemma density_step_support (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)
    (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    density G order d x p w r₀ n h.1 ω ≠ 0 ∧
    G.contactKernel order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
      (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2 ≠ 0 ∧
    side G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 = h.2.1 := by
  rw [density] at hr
  split_ifs at hr with hs
  · exact ⟨(mul_ne_zero_iff.mp hr).1,(mul_ne_zero_iff.mp hr).2,hs⟩
  · exact (hr rfl).elim

end ExactLaw

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySupport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*} (G : BondGraph V E)

lemma consistent_append (L : List (V × Bool)) (ω : Set E) (hL : Consistent G L ω)
    (a : V) (b : Bool) (hnew : ∀ z ∈ L, (G.openGraph ω).Reachable a z.1 → b=z.2) :
    Consistent G (L++[(a,b)]) ω := by
  intro z hz t ht hr
  rcases List.mem_append.mp hz with hz|hz <;> rcases List.mem_append.mp ht with ht|ht
  · exact hL z hz t ht hr
  · have he := List.mem_singleton.mp ht
    subst t
    exact (hnew z hz hr.symm).symm
  · have he := List.mem_singleton.mp hz
    subst z
    exact hnew t ht hr
  · have he := List.mem_singleton.mp hz
    subst z
    have he := List.mem_singleton.mp ht
    subst t
    rfl

lemma consistent_bases (u v : V) (ω : Set E) (h : ¬(G.openGraph ω).Reachable u v) :
    Consistent G [(u,true),(v,false)] ω := by
  intro z hz t ht hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ht
  rcases hz with rfl|rfl <;> rcases ht with rfl|rfl
  · rfl
  · exact (h hr).elim
  · exact (h hr.symm).elim
  · rfl

section Kernel
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma kernel_colour_consistent (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (a : V)
    (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order (anchorSet d x n h) a p w
      (G.clusterObject ω (anchorSet d x n h)) ω m ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (z : V × Bool) (hz : z ∈ anchors d x n h) (hr : (G.openGraph ω).Reachable a z.1) :
    side G (anchors d x n h) a ω m = z.2 := by
  have ha : a ∈ (G.clusterObject ω (anchorSet d x n h)).1 := ⟨z.1,⟨z.2,hz⟩,hr.symm⟩
  have hm : m=none := by
    by_contra hm
    simp only [contactKernel,ite_eq_left ha,ite_eq_right hm] at hk
    exact hk rfl
  subst m
  have hex := kernel_parent_exists G order d x n h a p w ω none hk
  obtain ⟨t,ht,hreach⟩ := firstIndex_spec hex
  have hparent : (anchors d x n h)[parent G (anchors d x n h) a ω none]? = some t := ht
  have hside : side G (anchors d x n h) a ω none = t.2 := by
    simp only [side,hparent,Option.getD_some]
  rw [hside]
  exact hL t (List.mem_of_getElem? ht) z hz (hreach.symm.trans hr)

lemma density_consistent (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (p : ℝ) (w : E → Prop → ℝ) (s : ℕ)
    (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    Consistent G (anchors d x n h) ω := by
  induction n with
  | zero =>
    have hE : endpointEvent G (x 0) (x d) s ω := by
      by_contra hE
      simp only [density,seed,ite_eq_right hE,mul_zero] at hr
      exact hr rfl
    exact consistent_bases G _ _ ω hE.1
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w _ n h ω hr
    have hL := ih h.1 hprev
    apply consistent_append G _ ω hL
    intro z hz hzreach
    rw [←hs]
    exact kernel_colour_consistent G order d x n h.1 _ p w ω _ hk hL z hz hzreach

end Kernel

lemma endpoint_labels (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (x (interval d n h).1,true) ∈ anchors d x n h ∧
      (x (interval d n h).2,false) ∈ anchors d x n h := by
  induction n with
  | zero => constructor <;> simp [anchors,interval]
  | succ n ih =>
    have hi := ih h.1
    by_cases ht : (interval d n h.1).2 ≤ (interval d n h.1).1+1
    · constructor
      · exact List.mem_append_left _ (by simpa only [interval,bisect,ite_eq_left ht] using hi.1)
      · exact List.mem_append_left _ (by simpa only [interval,bisect,ite_eq_left ht] using hi.2)
    · cases hb : h.2.1 <;>
        simp only [interval,bisect,hb,Bool.false_eq_true,↓reduceIte,anchors,
          List.mem_append,List.mem_singleton,nextIndex,ite_eq_right ht] <;>
        simp_all only [or_true,true_or,and_self]

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_AncestryForest
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

namespace Forest
variable (F : Forest)

lemma lineage_base {n : ℕ} (h : n < 2) : F.lineage n = [n] := by
  rw [lineage, dite_eq_left h]

lemma lineage_step {n : ℕ} (h : 2 ≤ n) : F.lineage n = n :: F.lineage (F.parent n) := by
  rw [lineage, dite_eq_right (by omega : ¬n<2)]

lemma self_mem_lineage (n : ℕ) : n ∈ F.lineage n := by
  rw [lineage]
  split_ifs <;> simp

lemma mem_lineage_le {a n : ℕ} (h : a ∈ F.lineage n) : a ≤ n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a = n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      exact he.le
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact le_rfl
      · exact (ih (F.parent n) (F.parent_lt n (by omega)) h).trans
          (F.parent_lt n (by omega)).le

lemma root_base {n : ℕ} (h : n < 2) : F.root n = n := by
  rw [root, dite_eq_left h]

lemma root_step {n : ℕ} (h : 2 ≤ n) : F.root n = F.root (F.parent n) := by
  rw [root, dite_eq_right (by omega : ¬n<2)]

lemma root_lt_two (n : ℕ) : F.root n < 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simpa only [F.root_base hn] using hn
    · rw [F.root_step (by omega : 2 ≤ n)]
      exact ih _ (F.parent_lt n (by omega))

lemma root_mem_lineage (n : ℕ) : F.root n ∈ F.lineage n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simp [F.root_base hn,F.lineage_base hn]
    · rw [F.root_step (by omega : 2 ≤ n),F.lineage_step (by omega : 2 ≤ n)]
      exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)))

lemma root_eq_of_mem {a n : ℕ} (h : a ∈ F.lineage n) : F.root a = F.root n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · rfl
      · rw [F.root_step (by omega : 2 ≤ n)]
        exact ih _ (F.parent_lt n (by omega)) h

lemma lineage_subset_of_mem {a n : ℕ} (h : a ∈ F.lineage n) :
    F.lineage a ⊆ F.lineage n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]; exact List.Subset.refl _
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact List.Subset.refl _
      · intro b hb
        rw [F.lineage_step (by omega : 2 ≤ n)]
        exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)) h hb)

lemma parent_mem_lineage {a n : ℕ} (ha : 2 ≤ a) (h : a ∈ F.lineage n) :
    F.parent a ∈ F.lineage n := by
  apply F.lineage_subset_of_mem h
  rw [F.lineage_step ha]
  exact List.mem_cons_of_mem _ (F.self_mem_lineage _)

lemma parent_injective_lineage {n a b : ℕ} (ha : a ∈ F.lineage n)
    (hb : b ∈ F.lineage n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (he : F.parent a = F.parent b) : a=b := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 2
    · have := F.mem_lineage_le ha
      omega
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at ha hb
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · rfl
      · have hle := F.mem_lineage_le hb
        have hlt := F.parent_lt b hb2
        omega
      · have hle := F.mem_lineage_le ha
        have hlt := F.parent_lt a ha2
        omega
      · exact ih _ (F.parent_lt n (by omega)) ha hb ha2 hb2 he

lemma parent_injective_two_lineages {u v a b : ℕ}
    (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.lineage u ∨ a ∈ F.lineage v)
    (hb : b ∈ F.lineage u ∨ b ∈ F.lineage v)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (he : F.parent a = F.parent b) : a=b := by
  rcases ha with ha|ha <;> rcases hb with hb|hb
  · exact F.parent_injective_lineage ha hb ha2 hb2 he
  · have h1 := F.root_eq_of_mem (F.parent_mem_lineage ha2 ha)
    have h2 := F.root_eq_of_mem (F.parent_mem_lineage hb2 hb)
    exact (huv (h1.symm.trans ((congrArg F.root he).trans h2))).elim
  · have h1 := F.root_eq_of_mem (F.parent_mem_lineage ha2 ha)
    have h2 := F.root_eq_of_mem (F.parent_mem_lineage hb2 hb)
    exact (huv (h2.symm.trans ((congrArg F.root he).symm.trans h1))).elim
  · exact F.parent_injective_lineage ha hb ha2 hb2 he

end Forest
end CriticalPercolation.InterpolationForest

namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

lemma mem_active {u v a : ℕ} : a ∈ F.active u v ↔
    (a ∈ F.lineage u ∨ a ∈ F.lineage v) ∧ 2 ≤ a := by
  simp [active]

lemma active_parent {u v a : ℕ} (ha : a ∈ F.active u v) :
    F.parent a < 2 ∨ F.parent a ∈ F.active u v := by
  by_cases hp : F.parent a < 2
  · exact Or.inl hp
  · apply Or.inr
    rw [mem_active] at ha ⊢
    exact ⟨ha.1.imp (F.parent_mem_lineage ha.2) (F.parent_mem_lineage ha.2),by omega⟩

lemma parent_injOn_active {u v : ℕ} (huv : F.root u ≠ F.root v) :
    Set.InjOn F.parent (↑(F.active u v) : Set ℕ) := by
  intro a ha b hb he
  rw [Finset.mem_coe,mem_active] at ha hb
  exact F.parent_injective_two_lineages huv ha.1 hb.1 ha.2 hb.2 he

theorem active_pair_multiplicity {u v : ℕ} (huv : F.root u ≠ F.root v) (a : ℕ) :
    ((F.active u v).filter fun b => b=a ∨ F.parent b=a).card ≤ 2 := by
  have h1 : ((F.active u v).filter fun b => b=a).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b hb c hc
    exact (Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm
  have h2 : ((F.active u v).filter fun b => F.parent b=a).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b hb c hc
    exact F.parent_injOn_active huv (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hc).1
      ((Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm)
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (by omega)

lemma previous_lineage_le_parent {n a b : ℕ} (ha : a ∈ F.lineage n)
    (hb : b ∈ F.lineage n) (ha2 : 2 ≤ a) (hba : b < a) : b ≤ F.parent a := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 2
    · have := F.mem_lineage_le ha
      omega
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at ha hb
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · omega
      · exact F.mem_lineage_le hb
      · have := F.mem_lineage_le ha
        have := F.parent_lt b (by omega : 2 ≤ b)
        omega
      · exact ih _ (F.parent_lt n (by omega)) ha hb ha2 hba

theorem previous_active_le_parent {u v a b : ℕ} (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.active u v) (hb : b ∈ F.active u v)
    (hside : F.root a = F.root b) (hba : b < a) : b ≤ F.parent a := by
  rw [mem_active] at ha hb
  rcases ha.1 with hau|hav <;> rcases hb.1 with hbu|hbv
  · exact F.previous_lineage_le_parent hau hbu ha.2 hba
  · exact (huv ((F.root_eq_of_mem hau).symm.trans (hside.trans (F.root_eq_of_mem hbv)))).elim
  · exact (huv ((F.root_eq_of_mem hbu).symm.trans (hside.symm.trans (F.root_eq_of_mem hav)))).elim
  · exact F.previous_lineage_le_parent hav hbv ha.2 hba

end CriticalPercolation.InterpolationForest.Forest
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryForest
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma nodeParent_old (d : ℕ) (x : ℕ → V) (ω : Set E) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : nodeParent G d x ω (n+1) h i = nodeParent G d x ω n h.1 i := by
  rw [nodeParent,ite_eq_right (by omega : i≠n+2)]

lemma node_old (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : node d x (n+1) h i = node d x n h.1 i := by
  change ((anchors d x n h.1 ++ [_])[i]?).getD _ = _
  rw [List.getElem?_append_left (by simpa only [anchors_length] using hi)]
  rfl

lemma node_current (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1)) :
    node d x (n+1) h (n+2) = (x (nextIndex d n h.1),h.2.1) := by
  unfold node anchors
  rw [List.getElem?_append_right (by simp [anchors_length])]
  simp only [anchors_length,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

lemma node_getElem? (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    (anchors d x n h)[i]? = some (node d x n h i) := by
  have hil : i<(anchors d x n h).length := by simpa only [anchors_length] using hi
  simp only [node,List.getElem?_eq_getElem hil,Option.getD_some]

lemma node_mem (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    node d x n h i ∈ anchors d x n h := List.mem_of_getElem? (node_getElem? d x n h i hi)

lemma node_bases (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    node d x n h 0 = (x 0,true) ∧ node d x n h 1 = (x d,false) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [node_old d x n h 0 (by omega),node_old d x n h 1 (by omega)]
    exact ih h.1

section Support
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_current (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    nodeParent G d x ω (n+1) h (n+2) =
      parent G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  have hp := parent_lt_of_exists G _ _ ω _
    (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
  rw [anchors_length] at hp
  simp only [nodeParent,if_true,ite_eq_left hp]

lemma node_colour_parent (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    (node d x n h i).2 = (node d x n h (nodeParent G d x ω n h i)).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i=n+2
    · subst i
      rw [node_current,nodeParent_current G order d x p w r₀ n h ω hr]
      have hp := parent_lt_of_exists G _ _ ω _
        (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
      rw [anchors_length] at hp
      rw [node_old d x n h _ hp]
      rw [← hs]
      simp only [side,node_getElem? d x n h.1 _ hp,Option.getD_some]
    · have hio : i < n+2 := by omega
      rw [node_old d x n h i hio,nodeParent_old G d x ω n h i hio,
        node_old d x n h _ ((nodeParent_lt G d x ω n h.1 i hi).trans hio)]
      exact ih h.1 hprev hio

lemma node_root_colour (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hin : i < n+2) :
    (node d x n h i).2 = if (historyForest G d x ω n h).root i = 0 then true else false := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < 2
    · rw [Forest.root_base _ hi]
      have hb := node_bases d x n h
      interval_cases i <;> simp only [hb.1,hb.2,if_true,one_ne_zero,if_false]
    · have hi2 : 2 ≤ i := by omega
      rw [Forest.root_step _ hi2]
      rw [node_colour_parent G order d x p w r₀ n h ω hr i hi2 hin]
      exact ih _ (nodeParent_lt G d x ω n h i hi2)
        ((nodeParent_lt G d x ω n h i hi2).trans hin)

end Support

lemma parent_canonical (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (hex : ∃ i, parentPredicate G L a ω m i) : Canonical G L ω (parent G L a ω m) := by
  intro j z t hj hz ht hr
  have hs := firstIndex_spec hex
  obtain ⟨v,hv,hpred⟩ := hs
  have hvt : v=t := Option.some.inj (hv.symm.trans ht)
  subst v
  have hP : parentPredicate G L a ω m j := by
    refine ⟨z,hz,?_⟩
    cases m with
    | none => exact hpred.trans hr.symm
    | some e =>
      obtain ⟨u,hu,htu⟩ := hpred
      exact ⟨u,hu,hr.trans htu⟩
  have hle := firstIndex_le hP
  exact (Nat.not_le_of_gt hj) hle

lemma canonical_append (L M : List (V × Bool)) (ω : Set E) (i : ℕ) (hi : i < L.length)
    (hC : Canonical G L ω i) : Canonical G (L++M) ω i := by
  intro j z t hj hz ht
  rw [List.getElem?_append_left (hj.trans hi)] at hz
  rw [List.getElem?_append_left hi] at ht
  exact hC j z t hj hz ht

lemma canonical_distinct (L : List (V × Bool)) (ω : Set E) (i j : ℕ)
    (hi : Canonical G L ω i) (hj : Canonical G L ω j)
    (z t : V × Bool) (hz : L[i]? = some z) (ht : L[j]? = some t)
    (hr : (G.openGraph ω).Reachable z.1 t.1) : i=j := by
  rcases lt_trichotomy i j with hij|hij|hij
  · exact (hj i z t hij hz ht hr).elim
  · exact hij
  · exact (hi j t z hij ht hz hr.symm).elim

section CanonicalSupport
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    Canonical G (anchors d x n h) ω (nodeParent G d x ω n h i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i = n+2
    · subst i
      rw [nodeParent_current G order d x p w r₀ n h ω hr]
      have hex := kernel_parent_exists G order d x n h.1 _ p w ω _ hk
      apply canonical_append
      · exact parent_lt_of_exists G _ _ ω _ hex
      · exact parent_canonical G _ _ ω _ hex
    · have hio : i < n+2 := by omega
      rw [nodeParent_old G d x ω n h i hio]
      apply canonical_append
      · rw [anchors_length]
        exact (nodeParent_lt G d x ω n h.1 i hi).trans hio
      · exact ih h.1 hprev hio

lemma lineage_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (j : ℕ) (hjn : j < n+2) (hj : Canonical G (anchors d x n h) ω j)
    (i : ℕ) (hi : i ∈ (historyForest G d x ω n h).lineage j) :
    Canonical G (anchors d x n h) ω i := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj2 : j < 2
    · have he : i=j := by simpa only [Forest.lineage_base _ hj2,List.mem_singleton] using hi
      exact he ▸ hj
    · have hj2' : 2 ≤ j := by omega
      rw [Forest.lineage_step _ hj2',List.mem_cons] at hi
      rcases hi with rfl|hi
      · exact hj
      · exact ih _ (nodeParent_lt G d x ω n h j hj2')
          ((nodeParent_lt G d x ω n h j hj2').trans hjn)
          (nodeParent_canonical G order d x p w r₀ n h ω hr j hj2' hjn) hi

end CanonicalSupport

lemma owner_exists (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    ∃ i, parentPredicate G (anchors d x n h) a ω none i := by
  obtain ⟨b,hb⟩ := ha
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hb
  exact ⟨i,(a,b),hi,.refl _⟩

lemma owner_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    owner G d x n h ω a < n+2 := by
  have hp := parent_lt_of_exists G _ _ ω none (owner_exists G d x n h ω a ha)
  simpa only [anchors_length,owner] using hp

lemma owner_canonical (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    Canonical G (anchors d x n h) ω (owner G d x n h ω a) :=
  parent_canonical G _ _ ω none (owner_exists G d x n h ω a ha)

lemma owner_reachable (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    (G.openGraph ω).Reachable a (node d x n h (owner G d x n h ω a)).1 := by
  obtain ⟨z,hz,hr⟩ := firstIndex_spec (owner_exists G d x n h ω a ha)
  have he : z = node d x n h (owner G d x n h ω a) := Option.some.inj
    (hz.symm.trans (node_getElem? d x n h _ (owner_lt G d x n h ω a ha)))
  exact he ▸ hr

lemma owner_colour (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (b : Bool) (ha : (a,b) ∈ anchors d x n h)
    (hL : Consistent G (anchors d x n h) ω) :
    (node d x n h (owner G d x n h ω a)).2 = b :=
  (hL (a,b) ha _ (node_mem d x n h _ (owner_lt G d x n h ω a ⟨b,ha⟩))
    (owner_reachable G d x n h ω a ⟨b,ha⟩)).symm

section Owners
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma terminal_roots (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
    (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).1)) = 0 ∧
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).2)) = 1 := by
  have hL := density_consistent G order d x p w s n h ω hr
  have he := endpoint_labels d x n h
  have hl := owner_colour G d x n h ω _ true he.1 hL
  have hr' := owner_colour G d x n h ω _ false he.2 hL
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨true,he.1⟩)] at hl
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨false,he.2⟩)] at hr'
  constructor
  · by_contra hz
    simp only [ite_eq_right hz] at hl
    cases hl
  · have hn := (historyForest G d x ω n h).root_lt_two
      (owner G d x n h ω (x (interval d n h).2))
    have hz : (historyForest G d x ω n h).root
        (owner G d x n h ω (x (interval d n h).2)) ≠ 0 := by
      intro hz
      simp only [ite_eq_left hz] at hr'
      cases hr'
    omega

end Owners

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryMarks
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

section Marks
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma canonical_node_reachable_eq (n : ℕ) (h : History E n) (ω : Set E)
    (i j : ℕ) (hin : i < n+2) (hjn : j < n+2)
    (hi : Canonical G (anchors d x n h) ω i) (hj : Canonical G (anchors d x n h) ω j)
    (hr : (G.openGraph ω).Reachable (node d x n h i).1 (node d x n h j).1) : i=j :=
  canonical_distinct G _ ω i j hi hj _ _ (node_getElem? d x n h i hin)
    (node_getElem? d x n h j hjn) hr

end Marks

lemma active_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (ω : Set E)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) : i < n+2 := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)

section Active
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma active_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) :
    Canonical G (anchors d x n h) ω i := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
      (owner_canonical G d x n h ω _ ⟨true,he.1⟩) i hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)
      (owner_canonical G d x n h ω _ ⟨false,he.2⟩) i hi

end Active
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryWords
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

lemma interval_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    interval d n (fromWords n b m) = interval d n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fromWords,interval,ih (Fin.init b) (Fin.init m) (Fin.init m')]

lemma nextIndex_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    nextIndex d n (fromWords n b m) = nextIndex d n (fromWords n b m') := by
  simp only [nextIndex,interval_fromWords d n b m m']

lemma anchors_fromWords (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m m' : Fin n → Option E) :
    anchors d x n (fromWords n b m) = anchors d x n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fromWords,anchors,ih (Fin.init b) (Fin.init m) (Fin.init m'),
      nextIndex_fromWords d n (Fin.init b) (Fin.init m) (Fin.init m')]

lemma anchors_sides (d : ℕ) (x : ℕ → V) (n : ℕ) (h h' : History E n)
    (hs : sides n h = sides n h') : anchors d x n h = anchors d x n h' := by
  conv_lhs => rw [←fromWords_sides_marks n h]
  conv_rhs => rw [←fromWords_sides_marks n h']
  rw [hs]
  exact anchors_fromWords d x n _ _ _

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Divergence
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

lemma mul_log_div_ge_sub {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hs : 0 < p → 0 < r) : p - r ≤ p * Real.log (p / r) := by
  rcases eq_or_lt_of_le hp with rfl | hp
  · simp only [zero_sub, zero_mul]
    exact neg_nonpos.mpr hr
  · have hr := hs hp
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hr hp)) hp.le
    rw [Real.log_div hr.ne' hp.ne'] at h
    rw [Real.log_div hp.ne' hr.ne']
    have he : p * (r / p - 1) = r - p := by field_simp
    rw [he] at h
    nlinarith

lemma mass_sub_le_divergence (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x) - (∑ x, R x) ≤ divergence P R := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => mul_log_div_ge_sub (hP x) (hR x) (hs x)

end CriticalPercolation.FiniteEntropy

open Set Real
open scoped Topology

namespace CriticalPercolation.FiniteEntropy

lemma mul_log_div_le {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) :
    r * Real.log (r/p) ≤ r * (r/p - 1) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp
  · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hr hp)) hr.le

theorem binaryDivergence_upper {p r : ℝ} (hp : p ∈ Ioo 0 1) (hr : r ∈ Icc 0 1) :
    binaryDivergence r p ≤ (r-p)^2 / (p*(1-p)) := by
  have hq : 0 < 1-p := sub_pos.mpr hp.2
  have h1 := mul_log_div_le hr.1 hp.1
  have h2 := mul_log_div_le (sub_nonneg.mpr hr.2) hq
  have he : r * (r/p-1) + (1-r)*((1-r)/(1-p)-1) = (r-p)^2/(p*(1-p)) := by
    field_simp [hp.1.ne', hq.ne']
    ring
  exact (add_le_add h1 h2).trans_eq he

lemma mul_log_div_eq {r p : ℝ} (hp : p ≠ 0) :
    r * Real.log (r / p) = r * Real.log r - r * Real.log p := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [Real.log_div hr hp]
    ring

lemma continuous_binaryRemainder (p : ℝ) : Continuous (binaryRemainder p) := by
  unfold binaryRemainder
  fun_prop

lemma binaryRemainder_eq {p : ℝ} (hp : p ∈ Ioo 0 1) (r : ℝ) :
    binaryRemainder p r = binaryDivergence r p - 2*(r-p)^2 := by
  unfold binaryRemainder binaryDivergence
  rw [mul_log_div_eq hp.1.ne', mul_log_div_eq (sub_pos.mpr hp.2).ne']
  ring

lemma hasDerivAt_binaryRemainder (p : ℝ) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt (binaryRemainder p)
      (Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p)) r := by
  have hid := hasDerivAt_id r
  have ho := (hasDerivAt_const r (1:ℝ)).sub hid
  have hmul := (Real.hasDerivAt_mul_log hr.1.ne').add
    ((Real.hasDerivAt_mul_log (sub_pos.mpr hr.2).ne').comp r ho)
  convert ((hmul.sub (hid.mul_const (Real.log p))).sub
    (ho.mul_const (Real.log (1-p)))).sub
      (((hid.sub_const p).pow 2).const_mul 2) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

lemma hasDerivAt_binaryRemainder_deriv (p : ℝ) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt
      (fun r => Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p))
      (r⁻¹ + (1-r)⁻¹ - 4) r := by
  have hid := hasDerivAt_id r
  have ho := (hasDerivAt_const r (1:ℝ)).sub hid
  convert (((((Real.hasDerivAt_log hr.1.ne').sub
    ((Real.hasDerivAt_log (sub_pos.mpr hr.2).ne').comp r ho)).sub_const
      (Real.log p)).add_const (Real.log (1-p))).sub
        ((hid.sub_const p).const_mul 4)) using 1 <;> first | rfl | ring

lemma binary_second_deriv_nonneg {r : ℝ} (hr : r ∈ Ioo 0 1) :
    0 ≤ r⁻¹ + (1-r)⁻¹ - 4 := by
  have hq : 0 < 1-r := sub_pos.mpr hr.2
  have he : r⁻¹ + (1-r)⁻¹ - 4 = (2*r-1)^2 / (r*(1-r)) := by
    field_simp [hr.1.ne', hq.ne']
    ring
  rw [he]
  exact div_nonneg (sq_nonneg _) (mul_pos hr.1 hq).le

lemma convexOn_binaryRemainder (p : ℝ) : ConvexOn ℝ (Icc 0 1) (binaryRemainder p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0:ℝ) 1)
    (continuous_binaryRemainder p).continuousOn
    (f' := fun r => Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p))
    (f'' := fun r => r⁻¹ + (1-r)⁻¹ - 4)
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_binaryRemainder p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_binaryRemainder_deriv p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact binary_second_deriv_nonneg hr

theorem binaryDivergence_lower {p r : ℝ} (hp : p ∈ Ioo 0 1) (hr : r ∈ Icc 0 1) :
    2*(r-p)^2 ≤ binaryDivergence r p := by
  have hconv := convexOn_binaryRemainder p
  have hder : HasDerivAt (binaryRemainder p) 0 p := by
    simpa using hasDerivAt_binaryRemainder p hp
  have hmin : binaryRemainder p p ≤ binaryRemainder p r := by
    rcases lt_trichotomy p r with h | rfl | h
    · have hs := hconv.le_slope_of_hasDerivAt ⟨hp.1.le, hp.2.le⟩ hr h hder
      rw [slope_def_field] at hs
      have ht := (le_div_iff₀ (sub_pos.mpr h)).mp hs
      simpa using ht
    · rfl
    · have hs := hconv.slope_le_of_hasDerivAt hr ⟨hp.1.le, hp.2.le⟩ h hder
      rw [slope_def_field] at hs
      have ht := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      linarith
  rw [binaryRemainder_eq hp, binaryRemainder_eq hp] at hmin
  have hz : binaryDivergence p p = 0 := by
    simp [binaryDivergence, hp.1.ne', (sub_pos.mpr hp.2).ne']
  rw [hz] at hmin
  nlinarith

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MulLogDivScaled
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation.FiniteEntropy

lemma mul_log_div_scaled {x c p : ℝ} (hx : 0 ≤ x) (hc : 0 < c) (hp : 0 < p) :
    c*((x/c)*Real.log ((x/c)/p)) = x*Real.log (x/p)-x*Real.log c := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  · rw [Real.log_div (div_pos hx hc).ne' hp.ne', Real.log_div hx.ne' hc.ne',
      Real.log_div hx.ne' hp.ne']
    field_simp
    ring

lemma binaryDivergence_mass_split {l r p : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hp : p ∈ Set.Ioo 0 1) :
    (l+r)*binaryDivergence (r/(l+r)) p +(l+r)*Real.log (l+r) =
      l*Real.log l+r*Real.log r-l*Real.log (1-p)-r*Real.log p := by
  by_cases hzero : l+r = 0
  · have hl0 : l = 0 := by linarith
    have hr0 : r = 0 := by linarith
    simp [hl0, hr0]
  · have hpos : 0 < l+r := lt_of_le_of_ne (add_nonneg hl hr) (Ne.symm hzero)
    have hcomp : 1-r/(l+r) = l/(l+r) := by field_simp; ring
    have h1 := mul_log_div_scaled hr hpos hp.1
    have h2 := mul_log_div_scaled hl hpos (sub_pos.mpr hp.2)
    unfold binaryDivergence
    rw [hcomp, mul_add, h1, h2, mul_log_div_eq hp.1.ne',
      mul_log_div_eq (sub_pos.mpr hp.2).ne']
    ring

variable {X : Type*} [Fintype X]
lemma divergence_scale_reference (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hs : ∀ x, 0 < P x → 0 < R x) {c : ℝ} (hc : 0 < c) :
    divergence P (fun x => c*R x) = divergence P R - (∑ x, P x)*Real.log c := by
  have ht (x : X) : P x*Real.log (P x/(c*R x)) =
      P x*Real.log (P x/R x)-P x*Real.log c := by
    rcases eq_or_lt_of_le (hP x) with hz | hp
    · simp [← hz]
    · have hr := hs x hp
      rw [Real.log_div hp.ne' (mul_pos hc hr).ne', Real.log_mul hc.ne' hr.ne',
        Real.log_div hp.ne' hr.ne']
      ring
  simp only [divergence, ht, Finset.sum_sub_distrib, ← Finset.sum_mul]

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryTree
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.QueryTree.nodeFintype _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation
open FiniteEntropy

universe u

namespace QueryTree
variable {E : Type u}

lemma reference_pos {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    ∀ (t : QueryTree E) (x : t.Leaf), 0 < t.reference p x := by
  intro t
  induction t with
  | stop => intro x; exact zero_lt_one
  | ask e left right hl hr =>
    intro x
    cases x with
    | inl x => exact mul_pos (sub_pos.mpr hp.2) (hl x)
    | inr x => exact mul_pos hp.1 (hr x)

lemma charge_mono {F H : ℝ → ℝ} (hFH : ∀ r ∈ Set.Icc (0:ℝ) 1, F r ≤ H r)
    (t : QueryTree E) (P : t.Leaf → ℝ) (hP : ∀ x, 0 ≤ P x) :
    t.charge F P ≤ t.charge H P := by
  induction t with
  | stop => rfl
  | ask e left right hl hr =>
    let l := ∑ x, P (Sum.inl x)
    let r := ∑ x, P (Sum.inr x)
    have hn : 0 ≤ l+r := add_nonneg (Finset.sum_nonneg fun x _ => hP (.inl x))
      (Finset.sum_nonneg fun x _ => hP (.inr x))
    have hb : r/(l+r) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact div_nonneg (Finset.sum_nonneg fun x _ => hP (.inr x)) hn
      · by_cases hz : l+r = 0
        · simp [hz]
        · apply (div_le_one (lt_of_le_of_ne hn (Ne.symm hz))).mpr
          have : 0 ≤ l := Finset.sum_nonneg fun x _ => hP (.inl x)
          linarith
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hFH _ hb) hn)
      (hl _ fun x => hP (.inl x))) (hr _ fun x => hP (.inr x))

lemma charge_const_mul (F : ℝ → ℝ) (c : ℝ) (t : QueryTree E) (P : t.Leaf → ℝ) :
    t.charge (fun r => c*F r) P = c*t.charge F P := by
  induction t with
  | stop => simp [charge]
  | ask e left right hl hr => simp only [charge, hl, hr]; ring

theorem divergence_reference_eq_charge {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (P : t.Leaf → ℝ) (hP : ∀ x, 0 ≤ P x) :
    divergence P (t.reference p) =
      t.charge (fun r => binaryDivergence r p) P + (∑ x, P x)*Real.log (∑ x, P x) := by
  induction t with
  | stop => simp [divergence, reference, charge, Leaf]
  | ask e left right hl hr =>
    let P₀ : left.Leaf → ℝ := fun x => P (Sum.inl x)
    let P₁ : right.Leaf → ℝ := fun x => P (Sum.inr x)
    have hb := binaryDivergence_mass_split
      (Finset.sum_nonneg (s := Finset.univ) (fun x _ => hP (.inl x)))
      (Finset.sum_nonneg (s := Finset.univ) (fun x _ => hP (.inr x))) hp
    change (∑ x : Sum left.Leaf right.Leaf, P x*Real.log (P x/(ask e left right).reference p x)) = _
    rw [Fintype.sum_sum_type]
    change divergence P₀ (fun x => (1-p)*left.reference p x) +
      divergence P₁ (fun x => p*right.reference p x) = _
    rw [divergence_scale_reference P₀ (left.reference p) (fun x => hP (.inl x))
      (fun x _ => reference_pos hp left x) (sub_pos.mpr hp.2),
      divergence_scale_reference P₁ (right.reference p) (fun x => hP (.inr x))
      (fun x _ => reference_pos hp right x) hp.1,
      hl P₀ (fun x => hP (.inl x)), hr P₁ (fun x => hP (.inr x))]
    change _ = _ + (∑ x : Sum left.Leaf right.Leaf, P x)*Real.log (∑ x : Sum left.Leaf right.Leaf, P x)
    rw [Fintype.sum_sum_type]
    dsimp only [charge, P₀, P₁]
    linarith

theorem divergence_reference_bounds {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (P : t.Leaf → ℝ) (hP : ∀ x, 0 ≤ P x) (hMass : ∑ x, P x = 1) :
    2*t.charge (fun r => (r-p)^2) P ≤ divergence P (t.reference p) ∧
    divergence P (t.reference p) ≤ (p*(1-p))⁻¹*t.charge (fun r => (r-p)^2) P := by
  rw [divergence_reference_eq_charge hp t P hP, hMass, Real.log_one, mul_zero, add_zero]
  constructor
  · have h := charge_mono (fun r hr => binaryDivergence_lower hp hr) t P hP
    rwa [charge_const_mul] at h
  · have h := charge_mono (fun r hr => binaryDivergence_upper hp hr) t P hP
    have heq : (fun r => (r-p)^2/(p*(1-p))) =
        (fun r => (p*(1-p))⁻¹*(r-p)^2) := by
      funext r; simp only [div_eq_mul_inv, mul_comm]
    rwa [heq, charge_const_mul] at h

lemma run_dependsOn [DecidableEq E] (t : QueryTree E) (used : Finset E) (hv : t.Valid used) :
    DependsOn t.run (↑used : Set E)ᶜ := by
  intro ω ω' hω
  induction t generalizing used with
  | stop => rfl
  | ask e left right hl hr =>
    have he : ω e = ω' e := hω e hv.1
    have hc : ∀ i ∈ (↑(insert e used) : Set E)ᶜ, ω i = ω' i := by
      intro i hi
      exact hω i (fun hu => hi (Finset.mem_insert_of_mem hu))
    simp only [run, he]
    split_ifs
    · exact congrArg Sum.inr (hr _ hv.2.2 hc)
    · exact congrArg Sum.inl (hl _ hv.2.1 hc)

lemma reads_disjoint [DecidableEq E] (t : QueryTree E) (used : Finset E)
    (hv : t.Valid used) (ω : E → Bool) : ∀ e ∈ t.reads ω, e ∉ used := by
  induction t generalizing used with
  | stop => simp [reads]
  | ask e left right hl hr =>
    intro f hf
    simp only [reads, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hv.1
    · split_ifs at hf with he
      · exact fun hu => hr _ hv.2.2 _ hf (Finset.mem_insert_of_mem hu)
      · exact fun hu => hl _ hv.2.1 _ hf (Finset.mem_insert_of_mem hu)

lemma reads_nodup [DecidableEq E] (t : QueryTree E) (used : Finset E)
    (hv : t.Valid used) (ω : E → Bool) : (t.reads ω).Nodup := by
  induction t generalizing used with
  | stop => simp [reads]
  | ask e left right hl hr =>
    simp only [reads, List.nodup_cons]
    split_ifs
    · exact ⟨fun he => reads_disjoint right _ hv.2.2 ω e he (Finset.mem_insert_self _ _),
        hr _ hv.2.2⟩
    · exact ⟨fun he => reads_disjoint left _ hv.2.1 ω e he (Finset.mem_insert_self _ _),
        hl _ hv.2.1⟩

end QueryTree
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PushMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteEntropy
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma pushMass_nonneg (f : X → Y) (P : X → ℝ) (hP : ∀ x, 0 ≤ P x) (y : Y) :
    0 ≤ pushMass f P y := by
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

lemma pushMass_sum (f : X → Y) (P : X → ℝ) :
    ∑ y, pushMass f P y = ∑ x, P x := by
  classical
  simp only [pushMass]
  rw [Finset.sum_comm]
  simp

lemma sum_pushMass_mul (f : X → Y) (P : X → ℝ) (g : Y → ℝ) :
    ∑ y, pushMass f P y * g y = ∑ x, P x * g (f x) := by
  classical
  simp only [pushMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

lemma log_sum_inequality (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x)*Real.log ((∑ x, P x)/(∑ x, R x)) ≤ divergence P R := by
  classical
  let A := ∑ x, P x
  let B := ∑ x, R x
  have hA : 0 ≤ A := Finset.sum_nonneg fun x _ => hP x
  rcases eq_or_lt_of_le hA with hA | hA
  · have hz : ∀ x, P x = 0 := by
      intro x
      have hx := Finset.single_le_sum (fun y _ => hP y) (Finset.mem_univ x)
      dsimp [A] at hA
      linarith [hP x]
    simp [hz, divergence]
  have hB : 0 < B := by
    obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
      by_contra! hn
      have ht := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
      exact (not_le_of_gt hA) ht
    exact (hs x hx).trans_le (Finset.single_le_sum (fun y _ => hR y) (Finset.mem_univ x))
  let S : X → ℝ := fun x => R x * (A/B)
  have hS : ∀ x, 0 ≤ S x := fun x => mul_nonneg (hR x) (div_pos hA hB).le
  have hpos : ∀ x, 0 < P x → 0 < S x := fun x hx => mul_pos (hs x hx) (div_pos hA hB)
  have hmass : ∑ x, S x = A := by
    simp only [S, ← Finset.sum_mul]
    change B * (A/B) = A
    field_simp
  have hb := mass_sub_le_divergence P S hP hS hpos
  have he : divergence P S = divergence P R - A*Real.log (A/B) := by
    have ht (x : X) : P x * Real.log (P x / S x) =
        P x * Real.log (P x / R x) - P x * Real.log (A/B) := by
      rcases eq_or_lt_of_le (hP x) with hz | hp
      · simp [← hz]
      · have hr := hs x hp
        simp only [S, Real.log_div hp.ne' (mul_pos hr (div_pos hA hB)).ne',
          Real.log_mul hr.ne' (div_pos hA hB).ne', Real.log_div hp.ne' hr.ne']
        ring
    simp only [divergence, ht, Finset.sum_sub_distrib, ← Finset.sum_mul, A]
  rw [hmass, he] at hb
  change A*Real.log (A/B) ≤ divergence P R
  dsimp [A] at hb ⊢
  linarith

theorem divergence_pushMass_le (f : X → Y) (P R : X → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hR : ∀ x, 0 ≤ R x)
    (hs : ∀ x, 0 < P x → 0 < R x) :
    divergence (pushMass f P) (pushMass f R) ≤ divergence P R := by
  classical
  have hf (y : Y) := log_sum_inequality
    (fun x => if f x = y then P x else 0) (fun x => if f x = y then R x else 0)
    (fun x => by split_ifs <;> simp_all) (fun x => by split_ifs <;> simp_all)
    (fun x hx => by split_ifs at hx ⊢ <;> simp_all)
  have ht (x : X) (y : Y) :
      (if f x = y then P x else 0) *
          Real.log ((if f x = y then P x else 0)/(if f x = y then R x else 0)) =
        if f x = y then P x * Real.log (P x / R x) else 0 := by
    split_ifs <;> simp
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hf y)
  simp only [divergence, ht] at hh
  rw [Finset.sum_comm] at hh
  simpa [pushMass, divergence] using hh

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BitWeight
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.QueryTree.nodeFintype _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma bitWeight_sum (p : ℝ) (e : E) : ∑ b, bitWeight p e b = 1 := by
  simp [bitWeight]

omit [Fintype E] in
lemma bitWeight_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 1) (e : E) (b : Bool) :
    0 ≤ bitWeight p e b := by cases b <;> simp [bitWeight, hp.1, hp.2]

lemma reference_eq_product_push (p : ℝ) (t : QueryTree E)
    (used : Finset E) (hv : t.Valid used) :
    pushMass t.run (density (bitWeight p)) = t.reference p := by
  classical
  induction t generalizing used with
  | stop =>
    funext x
    have : x = PUnit.unit := Subsingleton.elim _ _
    subst x
    simp only [pushMass, run, reference]
    exact sum_density _ (bitWeight_sum p)
  | ask e left right hl hr =>
    have hi (b : Bool) : DependsOn (fun ω : E → Bool => if ω e = b then (1:ℝ) else 0)
        ({e} : Set E) := by
      intro ω ω' hω
      dsimp only
      rw [hω e (Set.mem_singleton e)]
    have hc (u : QueryTree E) (hu : u.Valid (insert e used)) (x : u.Leaf) :
        DependsOn (fun ω => if u.run ω = x then (1:ℝ) else 0) ({e} : Set E)ᶜ := by
      intro ω ω' hω
      have heq : u.run ω = u.run ω' := run_dependsOn u _ hu (fun j hj =>
        hω j (by intro hje; have hje : j = e := hje; subst j
                 exact hj (Finset.mem_insert_self _ _)))
      dsimp only
      rw [heq]
    funext x
    cases x with
    | inl x =>
      have heq : (fun ω => if (ask e left right).run ω = Sum.inl x then (1:ℝ) else 0) =
          (fun ω => (if ω e = false then (1:ℝ) else 0) *
            (if left.run ω = x then 1 else 0)) := by
        funext ω
        cases he : ω e <;> simp [run, he]
      have hm : pushMass (ask e left right).run (density (bitWeight p)) (Sum.inl x) =
          expect (bitWeight p) (fun ω => if (ask e left right).run ω = Sum.inl x then 1 else 0) := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      rw [hm, heq, expect_indep _ (bitWeight_sum p) _ (hi false)
        (hc left hv.2.1 x)]
      have hev : expect (bitWeight p) (fun ω => if ω e = false then 1 else 0) =
          bitWeight p e false := by
        convert expect_eval_indicator (bitWeight p) (bitWeight_sum p) e false using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        split_ifs <;> simp_all
      rw [hev]
      have hm' : expect (bitWeight p) (fun ω => if left.run ω = x then 1 else 0) =
          pushMass left.run (density (bitWeight p)) x := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
      rw [hm', hl _ hv.2.1]
      rfl
    | inr x =>
      have heq : (fun ω => if (ask e left right).run ω = Sum.inr x then (1:ℝ) else 0) =
          (fun ω => (if ω e = true then (1:ℝ) else 0) *
            (if right.run ω = x then 1 else 0)) := by
        funext ω
        cases he : ω e <;> simp [run, he]
      have hm : pushMass (ask e left right).run (density (bitWeight p)) (Sum.inr x) =
          expect (bitWeight p) (fun ω => if (ask e left right).run ω = Sum.inr x then 1 else 0) := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      rw [hm, heq, expect_indep _ (bitWeight_sum p) _ (hi true)
        (hc right hv.2.2 x)]
      have hev : expect (bitWeight p) (fun ω => if ω e = true then 1 else 0) =
          bitWeight p e true := by
        convert expect_eval_indicator (bitWeight p) (bitWeight_sum p) e true using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        split_ifs <;> simp_all
      rw [hev]
      have hm' : expect (bitWeight p) (fun ω => if right.run ω = x then 1 else 0) =
          pushMass right.run (density (bitWeight p)) x := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
      rw [hm', hr _ hv.2.2]
      rfl

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Node
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma bitWeight_pos {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (e : E) (b : Bool) :
    0 < bitWeight p e b := by
  cases b <;> simp [bitWeight, hp.1, hp.2]

theorem transcript_divergence_le {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (hv : t.Valid ∅) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) :
    divergence (pushMass t.run P) (t.reference p) ≤ divergence P (density (bitWeight p)) := by
  rw [← reference_eq_product_push p t ∅ hv]
  exact divergence_pushMass_le t.run P _ hP
    (density_nonneg (bitWeight_nonneg ⟨hp.1.le, hp.2.le⟩))
    (fun ω _ => Finset.prod_pos fun e _ => bitWeight_pos hp e (ω e))

theorem quadratic_bias_budget {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (hv : t.Valid ∅) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (hMass : ∑ ω, P ω = 1) :
    2*t.charge (fun r => (r-p)^2) (pushMass t.run P) ≤
      divergence P (density (bitWeight p)) := by
  exact (divergence_reference_bounds hp t _ (pushMass_nonneg t.run P hP)
    (by rw [pushMass_sum, hMass])).1.trans (transcript_divergence_le hp t hv P hP)

theorem transcript_divergence_upper {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (hMass : ∑ ω, P ω = 1) :
    divergence (pushMass t.run P) (t.reference p) ≤
      (p*(1-p))⁻¹*t.charge (fun r => (r-p)^2) (pushMass t.run P) := by
  exact (divergence_reference_bounds hp t _ (pushMass_nonneg t.run P hP)
    (by rw [pushMass_sum, hMass])).2

end CriticalPercolation.QueryTree

namespace CriticalPercolation.QueryTree
variable {E : Type*}

lemma nodeMass_root (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (z : PUnit) :
    (ask e l r).nodeMass P (.inl z) =
      (∑ x, P (.inl x)) + ∑ x, P (.inr x) := by
  simp [nodeMass, response, Fintype.sum_sum_type]

lemma nodeTrueMass_root (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (z : PUnit) :
    (ask e l r).nodeTrueMass P (.inl z) = ∑ x, P (.inr x) := by
  simp [nodeTrueMass, response, Fintype.sum_sum_type]

lemma nodeMass_left (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : l.Node) :
    (ask e l r).nodeMass P (.inr (.inl n)) = l.nodeMass (fun x => P (.inl x)) n := by
  simp [nodeMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma nodeTrueMass_left (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : l.Node) :
    (ask e l r).nodeTrueMass P (.inr (.inl n)) = l.nodeTrueMass (fun x => P (.inl x)) n := by
  simp [nodeTrueMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma nodeMass_right (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : r.Node) :
    (ask e l r).nodeMass P (.inr (.inr n)) = r.nodeMass (fun x => P (.inr x)) n := by
  simp [nodeMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma nodeTrueMass_right (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : r.Node) :
    (ask e l r).nodeTrueMass P (.inr (.inr n)) = r.nodeTrueMass (fun x => P (.inr x)) n := by
  simp [nodeTrueMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma charge_eq_sum (F : ℝ → ℝ) (t : QueryTree E) (P : t.Leaf → ℝ) :
    t.charge F P = ∑ n, t.nodeMass P n * F (t.nodeTrueMass P n / t.nodeMass P n) := by
  induction t with
  | stop => simp [charge, Node]
  | ask e l r hl hr =>
    change _ = ∑ n : PUnit ⊕ (l.Node ⊕ r.Node), _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, nodeMass_root, nodeTrueMass_root,
      nodeMass_left, nodeTrueMass_left, nodeMass_right, nodeTrueMass_right]
    rw [← hl, ← hr]
    simp only [charge]
    ring

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Visits
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*}

lemma response_run (t : QueryTree E) (n : t.Node) (ω : E → Bool) :
    t.response n (t.run ω) = if t.visits n ω then some (ω (t.bit n)) else none := by
  induction t with
  | stop => exact PEmpty.elim n
  | ask e l r hl hr =>
    rcases n with n | n
    · cases he : ω e <;> simp [run, response, visits, bit, he]
    · rcases n with n | n
      · cases he : ω e
        · have ih := hl n
          simp only [run, he, Bool.false_eq_true, ↓reduceIte, visits, response, bit] at ih ⊢
          convert ih using 1
          all_goals try with_reducible_and_instances rfl
          split_ifs <;> simp_all
        · simp [run, visits, response, he]
      · cases he : ω e
        · simp [run, visits, response, he]
        · have ih := hr n
          simp only [run, he, ↓reduceIte, visits, response, bit] at ih ⊢
          convert ih using 1
          all_goals try with_reducible_and_instances rfl
          split_ifs <;> simp_all

lemma nodeMass_push [Fintype E] (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.nodeMass (pushMass t.run P) n = ∑ ω, if t.visits n ω then P ω else 0 := by
  have h := sum_pushMass_mul t.run P (fun x => if (t.response n x).isSome then (1:ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  unfold nodeMass visits
  convert h using 1
  all_goals try with_reducible_and_instances rfl

lemma nodeTrueMass_push [Fintype E] (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.nodeTrueMass (pushMass t.run P) n =
      ∑ ω, if t.visits n ω ∧ ω (t.bit n) = true then P ω else 0 := by
  have h := sum_pushMass_mul t.run P (fun x => if t.response n x = some true then (1:ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [nodeTrueMass, h]
  apply Finset.sum_congr rfl
  intro ω _
  rw [response_run]
  split_ifs <;> simp_all

lemma quadratic_charge_eq_sum (p : ℝ) (t : QueryTree E) (P : t.Leaf → ℝ) :
    t.charge (fun r => (r-p)^2) P =
      ∑ n, (t.nodeTrueMass P n - p*t.nodeMass P n)^2 / t.nodeMass P n := by
  rw [charge_eq_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hz : t.nodeMass P n = 0
  · simp [hz]
  · field_simp

end CriticalPercolation.QueryTree

namespace CriticalPercolation
universe u v w

namespace MarkedTree
variable {E : Type u} {A : Type v} {B : Type w}

lemma trace_map (f : A → B) (t : MarkedTree E A) (ω : E → Bool) :
    (t.map f).trace ω = (t.trace ω).map (fun x => (x.1, f x.2)) := by
  induction t with
  | stop => rfl
  | ask e a l r hl hr => cases h : ω e <;> simp [map, trace, h, hl, hr]

lemma trace_bits (t : MarkedTree E A) (ω : E → Bool) :
    (t.trace ω).map Prod.fst = t.bare.reads ω := by
  induction t with
  | stop => rfl
  | ask e a l r hl hr => cases h : ω e <;> simp [trace, bare, QueryTree.reads, h, hl, hr]

lemma trace_append (t s : MarkedTree E A) (ω : E → Bool) :
    (t.append s).trace ω = t.trace ω ++ s.trace ω := by
  induction t with
  | stop => rfl
  | ask e a l r hl hr => cases h : ω e <;> simp [append, trace, h, hl, hr]

lemma trace_sequence (ts : List (MarkedTree E A)) (ω : E → Bool) :
    (sequence ts).trace ω = (ts.map (fun t => t.trace ω)).flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [sequence, trace_append, ih]

variable [DecidableEq E]

lemma compatible_update (σ : Cache E) (ω : E → Bool) (hσ : Compatible σ ω) (e : E) :
    Compatible (Function.update σ e (some (ω e))) ω := by
  intro f b hb
  by_cases h : f = e
  · subst f
    simpa using hb
  · exact hσ f b (by simpa [Function.update, h] using hb)

lemma update_compatible_value (σ : Cache E) (e : E) (b : Bool) (h : σ e = some b) :
    Function.update σ e (some b) = σ := by
  ext f
  by_cases hf : f = e
  · subst f; simp [h]
  · simp [Function.update, hf]

lemma trace_cached (t : MarkedTree E A) (σ : Cache E) (ω : E → Bool)
    (hσ : Compatible σ ω) :
    (t.cached σ).trace ω = fresh ω σ (t.trace ω) := by
  induction t generalizing σ with
  | stop => rfl
  | ask e a l r hl hr =>
    cases hs : σ e with
    | none =>
      cases he : ω e
      · simpa [cached, hs, trace, he, fresh] using hl
          (Function.update σ e (some false)) (by simpa [he] using compatible_update σ ω hσ e)
      · simpa [cached, hs, trace, he, fresh] using hr
          (Function.update σ e (some true)) (by simpa [he] using compatible_update σ ω hσ e)
    | some b =>
      have he := hσ e b hs
      have hu := update_compatible_value σ e b hs
      cases b
      · simpa [cached, hs, trace, he, fresh, hu] using hl σ hσ
      · simpa [cached, hs, trace, he, fresh, hu] using hr σ hσ

variable [Fintype E]

omit [DecidableEq E] in
lemma mem_domain (σ : Cache E) (e : E) : e ∈ domain σ ↔ (σ e).isSome := by
  simp [domain]

lemma domain_update (σ : Cache E) (e : E) (b : Bool) :
    domain (Function.update σ e (some b)) = insert e (domain σ) := by
  ext f
  by_cases hf : f = e
  · subst f; simp [mem_domain]
  · simp [mem_domain, Function.update, hf]

lemma cached_valid (t : MarkedTree E A) (σ : Cache E) :
    (t.cached σ).bare.Valid (domain σ) := by
  induction t generalizing σ with
  | stop => trivial
  | ask e a l r hl hr =>
    cases hs : σ e with
    | none =>
      simp only [cached, hs, bare, QueryTree.Valid]
      refine ⟨?_, ?_, ?_⟩
      · simp [mem_domain, hs]
      · simpa only [domain_update σ e false] using hl (Function.update σ e (some false))
      · simpa only [domain_update σ e true] using hr (Function.update σ e (some true))
    | some b =>
      cases b
      · simpa only [cached, hs] using hl σ
      · simpa only [cached, hs] using hr σ

lemma cached_empty_valid (t : MarkedTree E A) :
    (t.cached (fun _ => none)).bare.Valid ∅ := by
  simpa [domain] using cached_valid t (fun _ => none)

end MarkedTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Select
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree
variable {E A : Type*} [DecidableEq E] [Fintype E]

lemma fresh_eq_select (ω : E → Bool) (σ : Cache E) (xs : List (E × A)) :
    fresh ω σ xs = select (domain σ) xs := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
    simp only [fresh, select, ih, domain_update]
    cases hs : σ x.1 with
    | none => simp [mem_domain, hs]
    | some b =>
      have hm : x.1 ∈ domain σ := by simp [mem_domain, hs]
      simp [hm, Finset.insert_eq_of_mem hm]

lemma trace_cached_select (t : MarkedTree E A) (σ : Cache E) (ω : E → Bool)
    (hσ : Compatible σ ω) :
    (t.cached σ).trace ω = select (domain σ) (t.trace ω) := by
  rw [trace_cached t σ ω hσ, fresh_eq_select]

omit [Fintype E] in
lemma mem_select (S : Finset E) (xs : List (E × A)) (x : E × A) :
    x ∈ select S xs → x ∈ xs := by
  induction xs generalizing S with
  | nil => simp [select]
  | cons y ys ih =>
    simp only [select]
    split_ifs with h
    · exact fun hm => List.mem_cons_of_mem _ (ih S hm)
    · intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hm)

omit [Fintype E] in
lemma select_append (S : Finset E) (xs ys : List (E × A)) :
    select S (xs ++ ys) = select S xs ++ select (S ∪ (xs.map Prod.fst).toFinset) ys := by
  induction xs generalizing S with
  | nil => simp [select]
  | cons x xs ih =>
    simp only [List.cons_append, select]
    by_cases hx : x.1 ∈ S
    · simp only [hx, ↓reduceIte, ih, List.map_cons, List.toFinset_cons]
      congr 2
      ext e
      simp only [Finset.mem_union, Finset.mem_insert]
      aesop
    · simp only [hx, ↓reduceIte, ih, List.cons_append, List.map_cons, List.toFinset_cons]
      congr 3
      ext e
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto

omit [Fintype E] in
lemma select_of_nodup (S : Finset E) (xs : List (E × A))
    (hn : (xs.map Prod.fst).Nodup) :
    select S xs = xs.filter (fun x => x.1 ∉ S) := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [select, List.filter_cons]
    by_cases hx : x.1 ∈ S
    · simp [hx, ih _ hn.2]
    · simp only [hx, ↓reduceIte, ih _ hn.2]
      congr 1
      apply List.filter_congr
      intro y hy
      have hne : y.1 ≠ x.1 := by
        intro h
        exact hn.1 (List.mem_map.mpr ⟨y, hy, h⟩)
      simp [hne]

end CriticalPercolation.MarkedTree

namespace CriticalPercolation.QueryTree
variable {E : Type*}

lemma map_bit_pathNodes (t : QueryTree E) (ω : E → Bool) :
    (t.pathNodes ω).map t.bit = t.reads ω := by
  induction t with
  | stop => rfl
  | ask e l r hl hr =>
    cases h : ω e <;> simp [pathNodes, reads, h, List.map_map, bit, hl, hr, Function.comp_def]

lemma mem_pathNodes (t : QueryTree E) (ω : E → Bool) (n : t.Node) :
    n ∈ t.pathNodes ω ↔ t.visits n ω := by
  induction t with
  | stop => exact PEmpty.elim n
  | ask e l r hl hr =>
    rcases n with a | (n | n)
    · cases a
      cases h : ω e <;> simp [pathNodes, visits, run, response, h]
    · cases h : ω e
      · simpa [pathNodes, visits, run, response, h] using hl n
      · simp [pathNodes, visits, run, response, h]
    · cases h : ω e
      · simp [pathNodes, visits, run, response, h]
      · simpa [pathNodes, visits, run, response, h] using hr n

lemma trace_marked (t : QueryTree E) (ω : E → Bool) :
    t.marked.trace ω = (t.pathNodes ω).map (fun n => (t.bit n, n)) := by
  induction t with
  | stop => rfl
  | ask e l r hl hr =>
    cases h : ω e <;>
      simp [marked, MarkedTree.trace, MarkedTree.trace_map, pathNodes, h,
        hl, hr, List.map_map, Function.comp_def, bit]

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Tagged
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree
open QueryTree

variable {E A : Type*}

lemma sum_visited_nodes (t : MarkedTree E A) (ω : E → Bool) (f : E → A → ℝ) :
    (∑ n : t.bare.Node, if t.bare.visits n ω then f (t.bare.bit n) (t.nodeLabel n) else 0) =
      ((t.trace ω).map (fun x => f x.1 x.2)).sum := by
  induction t with
  | stop =>
    change (∑ n : PEmpty, _) = 0
    simp
  | ask e a l r hl hr =>
    change (∑ n : PUnit ⊕ (l.bare.Node ⊕ r.bare.Node), _) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    cases h : ω e
    · simp only [Fintype.sum_unique, bare, QueryTree.visits, QueryTree.response, QueryTree.run,
        h, Bool.false_eq_true, ↓reduceIte, Option.isSome_some, QueryTree.bit,
        nodeLabel, Option.isSome_none, Finset.sum_const_zero, add_zero, trace, List.map_cons,
        List.sum_cons]
      congr 1
    · simp only [Fintype.sum_unique, bare, QueryTree.visits, QueryTree.response, QueryTree.run,
        h, ↓reduceIte, Option.isSome_some, QueryTree.bit,
        nodeLabel, Option.isSome_none, Bool.false_eq_true, Finset.sum_const_zero, zero_add,
        trace, List.map_cons, List.sum_cons]
      congr 1

lemma tagged_bit (coord : A → E) (t : MarkedTree E A) (ht : t.Tagged coord)
    (n : t.bare.Node) : t.bare.bit n = coord (t.nodeLabel n) := by
  induction t with
  | stop => exact PEmpty.elim n
  | ask e a l r hl hr =>
    rcases n with _ | (n | n)
    · exact ht.1
    · exact hl ht.2.1 n
    · exact hr ht.2.2 n

lemma tagged_map {B : Type*} (coord : B → E) (f : A → B) (t : MarkedTree E A)
    (ht : t.Tagged (coord ∘ f)) : (t.map f).Tagged coord := by
  induction t with
  | stop => trivial
  | ask e a l r hl hr => exact ⟨ht.1, hl ht.2.1, hr ht.2.2⟩

lemma tagged_append (coord : A → E) (t s : MarkedTree E A)
    (ht : t.Tagged coord) (hs : s.Tagged coord) : (t.append s).Tagged coord := by
  induction t with
  | stop => exact hs
  | ask e a l r hl hr => exact ⟨ht.1, hl ht.2.1, hr ht.2.2⟩

lemma tagged_sequence (coord : A → E) (ts : List (MarkedTree E A))
    (ht : ∀ t ∈ ts, t.Tagged coord) : (sequence ts).Tagged coord := by
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    apply tagged_append
    · exact ht t (by simp)
    · exact ih (fun s hs => ht s (List.mem_cons_of_mem _ hs))

variable [DecidableEq E]
lemma tagged_cached (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (σ : Cache E) : (t.cached σ).Tagged coord := by
  induction t generalizing σ with
  | stop => trivial
  | ask e a l r hl hr =>
    cases hs : σ e with
    | none =>
      simp only [cached, hs, Tagged]
      exact ⟨ht.1, hl ht.2.1 _, hr ht.2.2 _⟩
    | some b =>
      cases b
      · simpa only [cached, hs] using hl ht.2.1 σ
      · simpa only [cached, hs] using hr ht.2.2 σ

lemma mem_select_block (S : Finset E) (pre mid post : List (E × A)) (x : E × A)
    (hp : x ∉ pre) (hs : x ∉ post) (hm : (mid.map Prod.fst).Nodup) :
    x ∈ select S (pre ++ mid ++ post) ↔ x ∈ mid ∧ x.1 ∉ S ∪ (pre.map Prod.fst).toFinset := by
  rw [List.append_assoc, select_append, select_append]
  have hp' : x ∉ select S pre := fun h => hp (mem_select S pre x h)
  have hs' (U : Finset E) : x ∉ select U post := fun h => hs (mem_select U post x h)
  simp only [List.mem_append, hp', hs', false_or, or_false]
  rw [select_of_nodup _ _ hm]
  simp

end CriticalPercolation.MarkedTree

namespace CriticalPercolation.QueryTree
variable {E : Type*}
lemma tagged_marked (t : QueryTree E) : t.marked.Tagged t.bit := by
  induction t with
  | stop => trivial
  | ask e l r hl hr =>
    refine ⟨rfl, ?_, ?_⟩
    · apply MarkedTree.tagged_map
      exact hl
    · apply MarkedTree.tagged_map
      exact hr
end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_TraceTagged
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree
open QueryTree

variable {E A : Type*}

lemma trace_tagged (coord : A → E) (t : MarkedTree E A) (ht : t.Tagged coord)
    (ω : E → Bool) (x : E × A) (hx : x ∈ t.trace ω) : x.1 = coord x.2 := by
  induction t with
  | stop => simp [trace] at hx
  | ask e a l r hl hr =>
    cases he : ω e <;> simp only [trace, he, Bool.false_eq_true, ↓reduceIte,
        List.mem_cons] at hx
    · rcases hx with rfl | hx
      · exact ht.1
      · exact hl ht.2.1 hx
    · rcases hx with rfl | hx
      · exact ht.1
      · exact hr ht.2.2 hx

lemma trace_labels_nodup [DecidableEq E] (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (hv : t.bare.Valid ∅) (ω : E → Bool) :
    ((t.trace ω).map Prod.snd).Nodup := by
  have he : ((t.trace ω).map Prod.snd).map coord = (t.trace ω).map Prod.fst := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact (trace_tagged coord t ht ω x hx).symm
  apply List.Nodup.of_map coord
  rw [he, trace_bits]
  exact reads_nodup _ _ hv ω

lemma list_label_sum [DecidableEq A] (xs : List A) (hn : xs.Nodup) (a : A) (v : ℝ) :
    (xs.map (fun b => if b = a then v else 0)).sum = if a ∈ xs then v else 0 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons, ih hn.2]
    by_cases h : b = a
    · subst b
      simp [hn.1]
    · by_cases ha : a ∈ xs <;> simp [h, ha, Ne.symm h]

lemma sum_tagged_visits [DecidableEq E] [DecidableEq A] (coord : A → E)
    (t : MarkedTree E A) (ht : t.Tagged coord) (hv : t.bare.Valid ∅)
    (ω : E → Bool) (a : A) (v : E → ℝ) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then
      (if t.bare.visits n ω then v (t.bare.bit n) else 0) else 0) =
      if (coord a,a) ∈ t.trace ω then v (coord a) else 0 := by
  have hn := trace_labels_nodup coord t ht hv ω
  have hm : a ∈ (t.trace ω).map Prod.snd ↔ (coord a,a) ∈ t.trace ω := by
    constructor
    · intro ha
      rcases List.mem_map.mp ha with ⟨x,hx,hxa⟩
      have he : x = (coord a,a) := Prod.ext (by rw [trace_tagged coord t ht ω x hx, hxa]) hxa
      rwa [← he]
    · intro ha
      exact List.mem_map.mpr ⟨_,ha,rfl⟩
  calc
    _ = ∑ n : t.bare.Node, if t.bare.visits n ω then
        (if t.nodeLabel n = a then v (coord a) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [t.tagged_bit coord ht n]
      split_ifs <;> simp_all
    _ = ((t.trace ω).map (fun x => if x.2 = a then v (coord a) else 0)).sum :=
      sum_visited_nodes t ω (fun _ b => if b = a then v (coord a) else 0)
    _ = if a ∈ (t.trace ω).map Prod.snd then v (coord a) else 0 := by
      simpa only [List.map_map, Function.comp_def] using
        list_label_sum ((t.trace ω).map Prod.snd) hn a (v (coord a))
    _ = _ := by simp only [hm]

lemma pooled_input_sum [Fintype E] [DecidableEq E] [DecidableEq A]
    (coord : A → E) (t : MarkedTree E A) (ht : t.Tagged coord) (hv : t.bare.Valid ∅)
    (P : (E → Bool) → ℝ) (f : (E → Bool) → E → ℝ) (a : A) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then
      (∑ ω, if t.bare.visits n ω then P ω*f ω (t.bare.bit n) else 0) else 0) =
      ∑ ω, if (coord a,a) ∈ t.trace ω then P ω*f ω (coord a) else 0 := by
  trans ∑ n : t.bare.Node, ∑ ω, if t.nodeLabel n = a then
    (if t.bare.visits n ω then P ω*f ω (t.bare.bit n) else 0) else 0
  · apply Finset.sum_congr rfl
    intro n _
    by_cases h : t.nodeLabel n = a <;> simp [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  exact sum_tagged_visits coord t ht hv ω a (fun e => P ω*f ω e)

end CriticalPercolation.MarkedTree

open Set MeasureTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_LocalNode
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree

variable {E I : Type*} (t : I → QueryTree E)

lemma tagged_algorithm (i : I) : (algorithm t i).Tagged (coord t) := by
  apply tagged_map
  exact tagged_marked (t i)

lemma tagged_raw (order : List I) : (raw t order).Tagged (coord t) := by
  apply tagged_sequence
  intro s hs
  rcases List.mem_map.mp hs with ⟨i, _, rfl⟩
  exact tagged_algorithm t i

lemma trace_algorithm (i : I) (ω : E → Bool) :
    (algorithm t i).trace ω =
      ((t i).pathNodes ω).map (fun n => ((t i).bit n, Sigma.mk i n)) := by
  simp [algorithm, trace_map, trace_marked, List.map_map, Function.comp_def]

lemma bits_trace_algorithm (i : I) (ω : E → Bool) :
    ((algorithm t i).trace ω).map Prod.fst = (t i).reads ω := by
  rw [trace_algorithm, List.map_map]
  exact map_bit_pathNodes (t i) ω

lemma index_mem_trace_algorithm (i : I) (ω : E → Bool) (x : E × LocalNode t)
    (h : x ∈ (algorithm t i).trace ω) : x.2.1 = i := by
  rw [trace_algorithm] at h
  rcases List.mem_map.mp h with ⟨n, _, rfl⟩
  rfl

lemma mem_trace_algorithm_self (i : I) (n : (t i).Node) (ω : E → Bool) :
    ((t i).bit n, Sigma.mk i n) ∈ (algorithm t i).trace ω ↔ (t i).visits n ω := by
  rw [trace_algorithm]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨m, hm, hmn⟩
    have he : m = n := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hmn)).2
    subst m
    exact (mem_pathNodes (t i) ω n).mp hm
  · intro h
    exact List.mem_map.mpr ⟨n, (mem_pathNodes (t i) ω n).mpr h, rfl⟩

lemma trace_raw (order : List I) (ω : E → Bool) :
    (raw t order).trace ω = (order.map (fun i => (algorithm t i).trace ω)).flatten := by
  simp [raw, trace_sequence, List.map_map, Function.comp_def]

lemma index_mem_trace_raw (order : List I) (ω : E → Bool) (x : E × LocalNode t)
    (h : x ∈ (raw t order).trace ω) : x.2.1 ∈ order := by
  rw [trace_raw, List.mem_flatten] at h
  rcases h with ⟨xs, hxs, hx⟩
  rcases List.mem_map.mp hxs with ⟨i, hi, rfl⟩
  rwa [index_mem_trace_algorithm t i ω x hx]

lemma mem_bits_trace_raw (order : List I) (ω : E → Bool) (e : E) :
    e ∈ ((raw t order).trace ω).map Prod.fst ↔ ∃ i ∈ order, e ∈ (t i).reads ω := by
  rw [trace_raw]
  simp only [List.map_flatten, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨xs, ⟨ys, ⟨i, hi, rfl⟩, rfl⟩, he⟩
    exact ⟨i, hi, by simpa only [bits_trace_algorithm] using he⟩
  · rintro ⟨i, hi, he⟩
    refine ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, ?_⟩
    simpa only [bits_trace_algorithm] using he

lemma trace_raw_append (pre post : List I) (ω : E → Bool) :
    (raw t (pre++post)).trace ω = (raw t pre).trace ω ++ (raw t post).trace ω := by
  simp [trace_raw]

variable [DecidableEq E] [Fintype E]

lemma combined_valid (order : List I) : (combined t order).bare.Valid ∅ :=
  cached_empty_valid _

omit [Fintype E] in
lemma combined_tagged (order : List I) : (combined t order).Tagged (coord t) :=
  tagged_cached _ _ (tagged_raw t order) _

lemma trace_combined (order : List I) (ω : E → Bool) :
    (combined t order).trace ω = select ∅ ((raw t order).trace ω) := by
  rw [combined, trace_cached_select]
  · simp [domain]
  · intro e b h; simp at h

lemma fresh_local_node (pre post : List I) (i : I) (n : (t i).Node) (ω : E → Bool)
    (hi : i ∉ pre) (hi' : i ∉ post) (hv : (t i).Valid ∅) :
    ((t i).bit n, Sigma.mk i n) ∈ (combined t (pre++i::post)).trace ω ↔
      (t i).visits n ω ∧ ∀ j ∈ pre, (t i).bit n ∉ (t j).reads ω := by
  rw [trace_combined]
  have he : (raw t (pre++i::post)).trace ω =
      (raw t pre).trace ω ++ (algorithm t i).trace ω ++ (raw t post).trace ω := by
    rw [trace_raw_append]
    simp [raw, MarkedTree.sequence, trace_append, List.append_assoc]
  rw [he, mem_select_block]
  · rw [mem_trace_algorithm_self]
    simp only [Finset.empty_union, List.mem_toFinset, mem_bits_trace_raw, not_exists, not_and]
  · exact fun h => hi (index_mem_trace_raw t pre ω _ h)
  · exact fun h => hi' (index_mem_trace_raw t post ω _ h)
  · rw [bits_trace_algorithm]
    exact reads_nodup (t i) ∅ hv ω

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_OrderMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

lemma integral_sq_le_mass_mul (f : X → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real Set.univ * ∫ x, (f x)^2 ∂μ := by
  have hp (c : ℝ) : 0 ≤ μ.real Set.univ * (c*c) +
      (-2*(∫ x, f x ∂μ))*c + ∫ x, (f x)^2 ∂μ := by
    have hi : (∫ x, (f x-c)^2 ∂μ) =
        μ.real Set.univ * (c*c) + (-2*(∫ x, f x ∂μ))*c + ∫ x, (f x)^2 ∂μ := by
      calc
        (∫ x, (f x-c)^2 ∂μ) =
            ∫ x, ((f x)^2 - (2*c)*f x) + c*c ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by ring)
        _ = _ := by
          have ha := integral_add (hf2.sub (hf.const_mul (2*c))) (integrable_const (c*c))
          have hs := integral_sub hf2 (hf.const_mul (2*c))
          simp only [Pi.sub_apply] at ha
          rw [ha, hs, integral_const_mul, integral_const, smul_eq_mul]
          ring
    rw [← hi]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.Priority
open FiniteEntropy

variable {I : Type*} [Fintype I]

lemma orderMass_nonneg (o : Order I) : 0 ≤ orderMass o := integral_nonneg (fun _ => zero_le_one)
lemma orderSquare_nonneg (o : Order I) (i : I) : 0 ≤ orderSquare o i :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma orderWeight_sq_le (o : Order I) (i : I) :
    (orderWeight o i)^2 ≤ orderSquare o i * orderMass o := by
  have h := integral_sq_le_mass_mul (μ := law.restrict (cell o))
    (fun u : I → ℝ => endpointKernel (u i))
    (integrable_eval_continuous _ continuous_endpointKernel i).restrict
    (integrable_eval_continuous (fun r => (endpointKernel r)^2) (continuous_endpointKernel.pow 2) i).restrict
  simpa only [orderWeight, orderSquare, orderMass, integral_const, smul_eq_mul,
    mul_one, mul_comm, one_mul] using h

lemma sum_orderMass : (∑ o : Order I, orderMass o) = 1 := by
  rw [show (∑ o : Order I, orderMass o) = ∑ o : Order I, ∫ _u in cell o, (1:ℝ) ∂law from rfl,
    sum_integral_cells _ (integrable_const 1)]
  simp

lemma sum_orderSquare (i : I) : (∑ o : Order I, orderSquare o i) = 16 := by
  rw [show (∑ o : Order I, orderSquare o i) =
      ∑ o : Order I, ∫ u in cell o, (endpointKernel (u i))^2 ∂law from rfl,
    sum_integral_cells _ (integrable_eval_continuous (fun r => (endpointKernel r)^2) (continuous_endpointKernel.pow 2) i)]
  exact square_weight_integral i

lemma priorList_suffix (o : Order I) (i : I) :
    o.val = priorList o i ++ i::suffix o i ∧ i ∉ priorList o i ∧ i ∉ suffix o i :=
  (order_split o i).choose_spec.choose_spec

lemma not_before_iff (u : I → ℝ) (o : Order I) (hu : u ∈ cell o) {i j : I}
    (hji : j ≠ i) : j ∉ priorList o i ↔ u i < u j := by
  have he := (priorList_suffix o i).1
  have hb := before_iff u o hu he hji
  constructor
  · intro hn
    have hp := hu
    rw [cell, Set.mem_ofPred_eq, he, List.pairwise_append, List.pairwise_cons] at hp
    have hm := mem_order o j
    rw [he, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact False.elim (hn hm)
    · exact False.elim (hji hm)
    · exact hp.2.1.1 j hm
  · intro h hj
    exact lt_asymm (hb.mp hj) h

lemma first_iff_fresh (o : Order I) (i : I) (S : Finset {j : I // j ≠ i})
    (u : I → ℝ) (hu : u ∈ cell o) : First o i S ↔ u ∈ freshSet i S := by
  dsimp [First, freshSet]
  exact forall₂_congr (fun j _ => not_before_iff u o hu j.property)

lemma weighted_first_identity (i : I) (S : Finset {j : I // j ≠ i}) (hS : S.card ≤ 3) :
    (∑ o : Order I, if First o i S then orderWeight o i else 0) = 1 := by
  let F : (I → ℝ) → ℝ := (freshSet i S).indicator (fun u => endpointKernel (u i))
  have hf : Integrable F law :=
    (integrable_eval_continuous _ continuous_endpointKernel i).indicator (measurableSet_freshSet i S)
  have hi (o : Order I) : (∫ u in cell o, F u ∂law) =
      if First o i S then orderWeight o i else 0 := by
    by_cases h : First o i S
    · rw [ite_eq_left h]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_cell o)] with u hu
      exact Set.indicator_of_mem ((first_iff_fresh o i S u hu).mp h) _
    · rw [ite_eq_right h]
      trans ∫ u in cell o, (0:ℝ) ∂law
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_cell o)] with u hu
        exact Set.indicator_of_notMem (fun hm => h ((first_iff_fresh o i S u hu).mpr hm)) _
      · simp
  calc
    (∑ o : Order I, if First o i S then orderWeight o i else 0) =
        ∑ o : Order I, ∫ u in cell o, F u ∂law := by simp_rw [hi]
    _ = ∫ u, F u ∂law := sum_integral_cells F hf
    _ = 1 := by
      rw [show F = (freshSet i S).indicator (fun u => endpointKernel (u i)) from rfl,
        integral_indicator (measurableSet_freshSet i S)]
      exact weighted_fresh_identity i S hS

end CriticalPercolation.Priority

open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Users
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy

variable {E I : Type*} [Fintype I]

lemma mem_users (t : I → QueryTree E) (ω : E → Bool) (e : E) (i : I) :
    i ∈ users t ω e ↔ e ∈ (t i).reads ω := by simp [users]

lemma mem_otherUsers (t : I → QueryTree E) (i : I) (ω : E → Bool) (e : E)
    (j : {j : I // j ≠ i}) : j ∈ otherUsers t i ω e ↔ e ∈ (t j.val).reads ω := by
  simp [otherUsers, mem_users]

lemma otherUsers_card (t : I → QueryTree E) (i : I) (ω : E → Bool) (e : E)
    (hi : e ∈ (t i).reads ω) : (otherUsers t i ω e).card = (users t ω e).card - 1 := by
  rw [otherUsers, Finset.card_subtype]
  have he : (users t ω e).filter (fun j => j ≠ i) = (users t ω e).erase i := by
    ext j
    simp [and_comm]
  rw [he, Finset.card_erase_of_mem ((mem_users t ω e i).mpr hi)]

lemma visits_bit_mem (t : QueryTree E) (ω : E → Bool) (n : t.Node)
    (hn : t.visits n ω) : t.bit n ∈ t.reads ω := by
  rw [← map_bit_pathNodes]
  exact List.mem_map.mpr ⟨n, (mem_pathNodes t ω n).mpr hn, rfl⟩

lemma otherUsers_card_le_three (t : I → QueryTree E) (i : I) (ω : E → Bool)
    (n : (t i).Node) (hn : (t i).visits n ω) (h : (users t ω ((t i).bit n)).card ≤ 4) :
    (otherUsers t i ω ((t i).bit n)).card ≤ 3 := by
  rw [otherUsers_card t i ω _ (visits_bit_mem _ _ _ hn)]
  omega

lemma first_iff_no_prior (t : I → QueryTree E) (o : Order I) (i : I)
    (ω : E → Bool) (e : E) :
    First o i (otherUsers t i ω e) ↔ ∀ j ∈ priorList o i, e ∉ (t j).reads ω := by
  constructor
  · intro h j hj hr
    have hji : j ≠ i := fun he => (priorList_suffix o i).2.1 (he ▸ hj)
    exact h ⟨j,hji⟩ ((mem_otherUsers t i ω e ⟨j,hji⟩).mpr hr) hj
  · intro h j hj hjp
    exact h j.val hjp ((mem_otherUsers t i ω e j).mp hj)

variable [Fintype E]

lemma fresh_order_node (t : I → QueryTree E) (o : Order I) (i : I) (n : (t i).Node)
    (ht : (t i).Valid ∅) (ω : E → Bool) :
    (coord t ⟨i,n⟩, ⟨i,n⟩) ∈ (combined t o.val).trace ω ↔
      (t i).visits n ω ∧ First o i (otherUsers t i ω ((t i).bit n)) := by
  change ((t i).bit n, ⟨i,n⟩) ∈ (combined t o.val).trace ω ↔ _
  rw [(priorList_suffix o i).1]
  rw [fresh_local_node t _ _ _ _ _ (priorList_suffix o i).2.1 (priorList_suffix o i).2.2 ht]
  rw [first_iff_no_prior]

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_InputMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*} [Fintype E]

lemma inputMass_eq_sum (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.inputMass P n = ∑ ω, if t.visits n ω then P ω else 0 := nodeMass_push t P n

lemma inputNumerator_eq_sum (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.inputNumerator p P n =
      ∑ ω, if t.visits n ω then P ω*(bitValue ω (t.bit n)-p) else 0 := by
  rw [inputNumerator, nodeTrueMass_push, inputMass_eq_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  cases t.visits n ω <;> cases hb : ω (t.bit n) <;> simp [hb,bitValue] <;> ring

lemma inputMass_nonneg (t : QueryTree E) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (n : t.Node) : 0 ≤ t.inputMass P n := by
  rw [inputMass_eq_sum]
  apply Finset.sum_nonneg
  intro ω _; split_ifs; exact hP ω; exact le_rfl

lemma inputNumerator_eq_zero (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (n : t.Node) (hn : t.inputMass P n = 0) :
    t.inputNumerator p P n = 0 := by
  have ht : 0 ≤ t.nodeTrueMass (pushMass t.run P) n := by
    rw [nodeTrueMass_push]
    apply Finset.sum_nonneg
    intro ω _; split_ifs; exact hP ω; exact le_rfl
  have hl : t.nodeTrueMass (pushMass t.run P) n ≤ t.inputMass P n := by
    rw [nodeTrueMass_push, inputMass_eq_sum]
    apply Finset.sum_le_sum
    intro ω _
    split_ifs <;> simp_all
  unfold inputNumerator
  rw [hn]
  linarith

lemma charge_eq_input_sum (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ) :
    t.charge (fun r => (r-p)^2) (pushMass t.run P) =
      ∑ n, (t.inputNumerator p P n)^2 / t.inputMass P n :=
  quadratic_charge_eq_sum p t _

end CriticalPercolation.QueryTree

namespace CriticalPercolation.MarkedTree
open QueryTree FiniteEntropy

variable {E A : Type*} [Fintype E]

lemma pooled_inputMass (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (hv : t.bare.Valid ∅) (P : (E → Bool) → ℝ) (a : A) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then t.bare.inputMass P n else 0) =
      ∑ ω, if (coord a,a) ∈ t.trace ω then P ω else 0 := by
  simp_rw [inputMass_eq_sum]
  simpa only [mul_one] using pooled_input_sum coord t ht hv P (fun _ _ => 1) a

lemma pooled_inputNumerator (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (hv : t.bare.Valid ∅) (p : ℝ) (P : (E → Bool) → ℝ) (a : A) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then t.bare.inputNumerator p P n else 0) =
      ∑ ω, if (coord a,a) ∈ t.trace ω then P ω*(bitValue ω (coord a)-p) else 0 := by
  simp_rw [inputNumerator_eq_sum]
  exact pooled_input_sum coord t ht hv P (fun ω e => bitValue ω e-p) a

end CriticalPercolation.MarkedTree

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy

variable {E I : Type*} [Fintype E] [Fintype I]

lemma fresh_weighted_input (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4)
    (ω : E → Bool) (i : I) (n : (t i).Node) (c : ℝ) :
    (∑ o : Order I, orderWeight o i *
      (if (coord t ⟨i,n⟩, ⟨i,n⟩) ∈ (combined t o.val).trace ω then P ω*c else 0)) =
      if (t i).visits n ω then P ω*c else 0 := by
  simp_rw [fresh_order_node t _ i n (ht i) ω]
  by_cases hv : (t i).visits n ω
  · simp only [hv, true_and, ↓reduceIte]
    by_cases hz : P ω = 0
    · simp [hz]
    · have hs := otherUsers_card_le_three t i ω n hv (hover ω (lt_of_le_of_ne (hP ω) (Ne.symm hz)) _)
      have hw := weighted_first_identity i (otherUsers t i ω ((t i).bit n)) hs
      calc
        (∑ o : Order I, orderWeight o i *
            (if First o i (otherUsers t i ω ((t i).bit n)) then P ω*c else 0)) =
            (∑ o : Order I, if First o i (otherUsers t i ω ((t i).bit n)) then orderWeight o i else 0)*
              (P ω*c) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro o _
          split_ifs <;> simp
        _ = P ω*c := by rw [hw, one_mul]
  · simp [hv]

lemma weighted_pooled_numerator (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (p : ℝ) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4) (i : I) (n : (t i).Node) :
    (∑ o : Order I, orderWeight o i *
      ∑ g : (combined t o.val).bare.Node, if (combined t o.val).nodeLabel g = ⟨i,n⟩ then
        (combined t o.val).bare.inputNumerator p P g else 0) =
      (t i).inputNumerator p P n := by
  have hpool (o : Order I) := pooled_inputNumerator (coord t) (combined t o.val)
    (combined_tagged t o.val) (combined_valid t o.val) p P (⟨i,n⟩ : LocalNode t)
  simp_rw [hpool, Finset.mul_sum]
  rw [Finset.sum_comm, inputNumerator_eq_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact fresh_weighted_input t ht P hP hover ω i n (bitValue ω ((t i).bit n)-p)

lemma pooled_mass_le (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (o : Order I) (i : I) (n : (t i).Node) :
    (∑ g : (combined t o.val).bare.Node, if (combined t o.val).nodeLabel g = ⟨i,n⟩ then
      (combined t o.val).bare.inputMass P g else 0) ≤ (t i).inputMass P n := by
  rw [pooled_inputMass (coord t) (combined t o.val) (combined_tagged t o.val)
    (combined_valid t o.val) P (⟨i,n⟩ : LocalNode t), inputMass_eq_sum]
  apply Finset.sum_le_sum
  intro ω _
  simp only [fresh_order_node t o i n (ht i) ω]
  split_ifs <;> simp_all

lemma weighted_pooled_mass_le (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (i : I) (n : (t i).Node) :
    (∑ o : Order I, orderSquare o i *
      ∑ g : (combined t o.val).bare.Node, if (combined t o.val).nodeLabel g = ⟨i,n⟩ then
        (combined t o.val).bare.inputMass P g else 0) ≤ 16*(t i).inputMass P n := by
  calc
    _ ≤ ∑ o : Order I, orderSquare o i * (t i).inputMass P n :=
      Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left
        (pooled_mass_le t ht P hP o i n) (orderSquare_nonneg o i))
    _ = _ := by rw [← Finset.sum_mul, sum_orderSquare]

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedCauchy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
variable {X A : Type*} [Fintype X] [Fintype A]

lemma pooled_two_weight_bound (tag : X → A) (z u v : X → ℝ) (L Z : A → ℝ) {C : ℝ}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hz : ∀ x, (z x)^2 ≤ u x*v x) (hL : ∀ a, 0 ≤ L a) (hC : 0 ≤ C)
    (hZ : ∀ a, Z a = ∑ x, if tag x = a then z x else 0)
    (hcost : ∀ a, (∑ x, if tag x = a then u x else 0) ≤ C*L a) :
    (∑ a, (Z a)^2 / L a) ≤ C * ∑ x, v x := by
  have hpoint (a : A) : (Z a)^2 / L a ≤
      C * ∑ x, if tag x = a then v x else 0 := by
    have hcs : (∑ x, if tag x = a then z x else 0)^2 ≤
        (∑ x, if tag x = a then u x else 0)*
        (∑ x, if tag x = a then v x else 0) := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro x _; split_ifs; exact hu x; exact le_rfl
      · intro x _; split_ifs; exact hv x; exact le_rfl
      · intro x _; split_ifs; exact hz x; norm_num
    rw [← hZ a] at hcs
    have hnon : 0 ≤ ∑ x, if tag x = a then v x else 0 := by
      apply Finset.sum_nonneg
      intro x _; split_ifs; exact hv x; exact le_rfl
    rcases eq_or_lt_of_le (hL a) with he | hp
    · rw [← he, div_zero]
      exact mul_nonneg hC hnon
    · apply (div_le_iff₀ hp).mpr
      calc
        (Z a)^2 ≤ (∑ x, if tag x = a then u x else 0)*
            (∑ x, if tag x = a then v x else 0) := hcs
        _ ≤ (C*L a)*(∑ x, if tag x = a then v x else 0) :=
          mul_le_mul_of_nonneg_right (hcost a) hnon
        _ = _ := by ring
  calc
    (∑ a, (Z a)^2/L a) ≤ ∑ a, C*∑ x, if tag x = a then v x else 0 :=
      Finset.sum_le_sum (fun a _ => hpoint a)
    _ = C * ∑ x, v x := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_GlobalNode
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy FiniteProduct

variable {E I : Type*} [Fintype E] [Fintype I]

omit [Fintype E] in
lemma pooled_weighted_sum (t : I → QueryTree E) (w : Order I → I → ℝ)
    (f : GlobalNode t → ℝ) (a : LocalNode t) :
    (∑ x : GlobalNode t, if globalTag t x = a then w x.1 (globalTag t x).1 * f x else 0) =
      ∑ o : Order I, w o a.1 * ∑ g : (combined t o.val).bare.Node,
        if (combined t o.val).nodeLabel g = a then f ⟨o,g⟩ else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h : globalTag t ⟨o,g⟩ = a
  · simp only [h, ite_eq_left]
  · simp only [h, if_false, mul_zero]

lemma weighted_node_square_bound (t : I → QueryTree E) (p : ℝ)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (x : GlobalNode t) :
    (orderWeight x.1 (globalTag t x).1 * (combined t x.1.val).bare.inputNumerator p P x.2)^2 ≤
      (orderSquare x.1 (globalTag t x).1 * (combined t x.1.val).bare.inputMass P x.2) *
      (orderMass x.1 * (combined t x.1.val).bare.inputNumerator p P x.2 ^ 2 /
        (combined t x.1.val).bare.inputMass P x.2) := by
  let M := (combined t x.1.val).bare.inputMass P x.2
  let N := (combined t x.1.val).bare.inputNumerator p P x.2
  have hM : 0 ≤ M := inputMass_nonneg _ P hP x.2
  change (orderWeight x.1 (globalTag t x).1 * N)^2 ≤
    (orderSquare x.1 (globalTag t x).1 * M)*(orderMass x.1*N^2/M)
  rcases eq_or_lt_of_le hM with hz | hp
  · have hN : N = 0 := inputNumerator_eq_zero _ p P hP x.2 hz.symm
    simp [hN]
  · have hh := mul_le_mul_of_nonneg_right (orderWeight_sq_le x.1 (globalTag t x).1)
      (sq_nonneg N)
    calc
      _ = (orderWeight x.1 (globalTag t x).1)^2 * N^2 := by ring
      _ ≤ (orderSquare x.1 (globalTag t x).1 * orderMass x.1)*N^2 := hh
      _ = _ := by field_simp

theorem overlap_four_charge (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (p : ℝ) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4) :
    (∑ i, (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P)) ≤
      16 * ∑ o : Order I, orderMass o *
        (combined t o.val).bare.charge (fun r => (r-p)^2)
          (pushMass (combined t o.val).bare.run P) := by
  let M (x : GlobalNode t) := (combined t x.1.val).bare.inputMass P x.2
  let N (x : GlobalNode t) := (combined t x.1.val).bare.inputNumerator p P x.2
  let z (x : GlobalNode t) := orderWeight x.1 (globalTag t x).1 * N x
  let u (x : GlobalNode t) := orderSquare x.1 (globalTag t x).1 * M x
  let v (x : GlobalNode t) := orderMass x.1 * (N x)^2 / M x
  have h := pooled_two_weight_bound (globalTag t) z u v
    (fun a : LocalNode t => (t a.1).inputMass P a.2)
    (fun a : LocalNode t => (t a.1).inputNumerator p P a.2)
    (C := 16)
    (fun x => mul_nonneg (orderSquare_nonneg _ _) (inputMass_nonneg _ P hP _))
    (fun x => div_nonneg (mul_nonneg (orderMass_nonneg _) (sq_nonneg _))
      (inputMass_nonneg _ P hP _))
    (weighted_node_square_bound t p P hP)
    (fun a => inputMass_nonneg _ P hP _) (by norm_num) ?_ ?_
  · convert h using 1
    · rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      exact charge_eq_input_sum (t i) p P
    · rw [Fintype.sum_sigma]
      congr 1
      apply Finset.sum_congr rfl
      intro o _
      rw [charge_eq_input_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      dsimp [v,N,M]
      ring
  · intro a
    exact (weighted_pooled_numerator t ht p P hP hover a.1 a.2).symm.trans
      (pooled_weighted_sum t orderWeight N a).symm
  · intro a
    exact (pooled_weighted_sum t orderSquare M a).trans_le
      (weighted_pooled_mass_le t ht P hP a.1 a.2)

theorem overlap_four_entropy {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hMass : ∑ ω, P ω = 1)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4) :
    (∑ i, divergence (pushMass (t i).run P) ((t i).reference p)) ≤
      16/(2*p*(1-p)) * divergence P (density (bitWeight p)) := by
  have hc := overlap_four_charge t ht p P hP hover
  have hb : 2*(∑ o : Order I, orderMass o *
      (combined t o.val).bare.charge (fun r => (r-p)^2)
        (pushMass (combined t o.val).bare.run P)) ≤ divergence P (density (bitWeight p)) := by
    calc
      _ = ∑ o : Order I, orderMass o * (2*
            (combined t o.val).bare.charge (fun r => (r-p)^2)
              (pushMass (combined t o.val).bare.run P)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro o _; ring
      _ ≤ ∑ o : Order I, orderMass o * divergence P (density (bitWeight p)) := by
        apply Finset.sum_le_sum
        intro o _
        exact mul_le_mul_of_nonneg_left
          (quadratic_bias_budget hp _ (combined_valid t o.val) P hP hMass) (orderMass_nonneg o)
      _ = _ := by rw [← Finset.sum_mul, sum_orderMass, one_mul]
  have hlocal : (∑ i, (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P)) ≤
      8 * divergence P (density (bitWeight p)) := by linarith
  calc
    _ ≤ ∑ i, (p*(1-p))⁻¹ * (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P) :=
      Finset.sum_le_sum (fun i _ => transcript_divergence_upper hp (t i) P hP hMass)
    _ = (p*(1-p))⁻¹ * ∑ i, (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (p*(1-p))⁻¹ * (8 * divergence P (density (bitWeight p))) :=
      mul_le_mul_of_nonneg_left hlocal (inv_nonneg.mpr (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)))
    _ = _ := by field_simp; ring

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_State
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
lemma eligible_succ (G : BondGraph V E) (st : State V E) (h : ∃ e, eligible G st e) :
    eligible G st (Classical.choose h) := Classical.choose_spec h

lemma compile_valid (G : BondGraph V E) (n : ℕ) (st : State V E) :
    (compile G n st).Valid st.read := by
  induction n generalizing st with
  | zero => trivial
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · exact ⟨(eligible_succ G st h).1, ih _, ih _⟩
    · trivial

omit [DecidableEq V] [DecidableEq E] in
lemma edge_reachable (G : BondGraph V E) (ω : E → Bool) {e : E} (he : ω e = true)
    {v t : V} (hv : v ∈ G.ends e) (ht : t ∈ G.ends e) :
    (G.openGraph {e | ω e = true}).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e,he,(Sym2.mem_and_mem_iff hne).mp ⟨hv,ht⟩⟩,hne⟩)

omit [DecidableEq V] in
lemma consistent_closed (G : BondGraph V E) (st : State V E) (ω : E → Bool) (e : E)
    (h : Consistent G st ω) (he : ω e ≠ true) : Consistent G (closed st e) ω := by
  intro f hf hw v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact (he hw).elim
  · exact h f hf hw v hv

lemma consistent_opened (G : BondGraph V E) (st : State V E) (ω : E → Bool) (e : E)
    (h : Consistent G st ω) : Consistent G (opened G st e) ω := by
  intro f hf hw v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact Finset.mem_union_right _ (Sym2.mem_toFinset.mpr hv)
  · exact Finset.mem_union_left _ (h f hf hw v hv)

lemma sound_opened (G : BondGraph V E) (S : Set V) (st : State V E) (ω : E → Bool) (e : E)
    (h : Sound G S st ω) (hel : eligible G st e) (he : ω e = true) :
    Sound G S (opened G st e) ω := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact h v hv
  · obtain ⟨u,hu,hue⟩ := hel.2
    obtain ⟨s,hs,hsu⟩ := h u hu
    exact ⟨s,hs,hsu.trans (edge_reachable G ω he hue (Sym2.mem_toFinset.mp hv))⟩

lemma compile_invariants (G : BondGraph V E) (S : Set V) (n : ℕ) (st : State V E)
    (ω : E → Bool) (hc : Consistent G st ω) (hs : Sound G S st ω) :
    Consistent G ((compile G n st).run ω) ω ∧
      Sound G S ((compile G n st).run ω) ω ∧
      st.reached ⊆ ((compile G n st).run ω).reached := by
  induction n generalizing st with
  | zero => exact ⟨hc,hs,Finset.Subset.refl _⟩
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.run]
      split_ifs with he
      · obtain ⟨hc',hs',hm⟩ := ih (opened G st (Classical.choose h))
          (consistent_opened G st ω _ hc)
          (sound_opened G S st ω _ hs (eligible_succ G st h) he)
        exact ⟨hc',hs',Finset.Subset.trans Finset.subset_union_left hm⟩
      · exact ih (closed st (Classical.choose h)) (consistent_closed G st ω _ hc he) hs
    · exact ⟨hc,hs,Finset.Subset.refl _⟩

lemma compile_read (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool) :
    ((compile G n st).run ω).read = st.read ∪ ((compile G n st).reads ω).toFinset := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.reads]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.run,SearchTree.reads]
      split_ifs with he
      · rw [ih]
        simp only [opened,List.toFinset_cons]
        simp only [Finset.insert_union,Finset.union_insert]
      · rw [ih]
        simp only [closed,List.toFinset_cons]
        simp only [Finset.insert_union,Finset.union_insert]
    · simp [SearchTree.run,SearchTree.reads]

variable [Fintype E]

lemma compile_exhausted (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool)
    (hbudget : Fintype.card E ≤ n + st.read.card) :
    ¬∃ e, eligible G ((compile G n st).run ω) e := by
  induction n generalizing st with
  | zero =>
    rintro ⟨e,he,_⟩
    have hec := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ st.read,fun h => he (h ▸ Finset.mem_univ e)⟩)
    simp only [Finset.card_univ] at hec
    omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      have he := (eligible_succ G st h).1
      have hc : Fintype.card E ≤ n + (insert (Classical.choose h) st.read).card := by
        rw [Finset.card_insert_of_notMem he]
        omega
      rw [SearchTree.run]
      split_ifs
      · exact ih _ hc
      · exact ih _ hc
    · exact h

lemma compile_reads_incident (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool)
    (hc : Consistent G st ω) (hs : Sound G Set.univ st ω) :
    ∀ e ∈ (compile G n st).reads ω,
      ∃ v ∈ ((compile G n st).run ω).reached, v ∈ G.ends e := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.reads]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.reads,SearchTree.run]
      by_cases he : ω (Classical.choose h) = true
      · simp only [he,↓reduceIte,List.mem_cons]
        intro e hem
        rcases hem with rfl | hem
        · obtain ⟨v,hv,hve⟩ := (eligible_succ G st h).2
          have hm := (compile_invariants G Set.univ n (opened G st (Classical.choose h)) ω
            (consistent_opened G st ω _ hc)
            (sound_opened G Set.univ st ω _ hs (eligible_succ G st h) he)).2.2
          exact ⟨v,hm (Finset.mem_union_left _ hv),hve⟩
        · exact ih _ (consistent_opened G st ω _ hc)
            (sound_opened G Set.univ st ω _ hs (eligible_succ G st h) he) e hem
      · simp only [he,List.mem_cons]
        intro e hem
        rcases hem with rfl | hem
        · obtain ⟨v,hv,hve⟩ := (eligible_succ G st h).2
          have hm := (compile_invariants G Set.univ n (closed st (Classical.choose h)) ω
            (consistent_closed G st ω _ hc he) hs).2.2
          exact ⟨v,hm hv,hve⟩
        · exact ih _ (consistent_closed G st ω _ hc he) hs e hem
    · simp [SearchTree.reads]

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Initial2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.QueryTree.nodeFintype _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
lemma initial_consistent (G : BondGraph V E) (S : Finset V) (ω : E → Bool) :
    Consistent G (initial S) ω := by
  intro e he
  exact (Finset.notMem_empty e he).elim

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
lemma initial_sound (G : BondGraph V E) (S : Finset V) (ω : E → Bool) :
    Sound G (S : Set V) (initial S) ω := by
  intro v hv
  exact ⟨v,hv,.refl _⟩

lemma search_reached (G : BondGraph V E) (S : Finset V) (ω : E → Bool) (v : V) :
    v ∈ ((search G S).run ω).reached ↔
      ∃ a ∈ S, (G.openGraph {e | ω e = true}).Reachable a v := by
  obtain ⟨hc,hs,hm⟩ := compile_invariants G (S : Set V) (Fintype.card E) (initial S) ω
    (initial_consistent G S ω) (initial_sound G S ω)
  constructor
  · exact hs v
  · rintro ⟨a,ha,hav⟩
    have he := compile_exhausted G (Fintype.card E) (initial S) ω (by simp [initial])
    have hcl : ∀ u ∈ ((search G S).run ω).reached, ∀ t,
        (G.openGraph {e | ω e = true}).Adj u t → t ∈ ((search G S).run ω).reached := by
      intro u hu t hut
      obtain ⟨⟨e,hew,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hut
      have hread : e ∈ ((search G S).run ω).read := by
        by_contra hn
        exact he ⟨e,hn,u,hu,by simp [heq]⟩
      exact hc e hread hew t (by simp [heq])
    have hh := ((G.openGraph {e | ω e = true}).reachable_iff_reflTransGen a v).mp hav
    clear hav
    induction hh with
    | refl => exact hm ha
    | tail _ huv ih => exact hcl _ ih _ huv

lemma search_reads (G : BondGraph V E) (S : Finset V) (ω : E → Bool) (e : E) :
    e ∈ (search G S).reads ω ↔
      ∃ v ∈ G.ends e, ∃ a ∈ S, (G.openGraph {e | ω e = true}).Reachable a v := by
  have he := compile_exhausted G (Fintype.card E) (initial S) ω (by simp [initial])
  have hrd : ((search G S).run ω).read = ((search G S).reads ω).toFinset := by
    simpa only [search,initial,Finset.empty_union] using compile_read G (Fintype.card E) (initial S) ω
  constructor
  · intro hed
    have hs : Sound G Set.univ (initial S) ω := by
      intro v _
      exact ⟨v,Set.mem_univ _,.refl _⟩
    obtain ⟨v,hv,hev⟩ := compile_reads_incident G (Fintype.card E) (initial S) ω
      (initial_consistent G S ω) hs e hed
    exact ⟨v,hev,(search_reached G S ω v).mp hv⟩
  · rintro ⟨v,hve,a,ha,hav⟩
    have hv := (search_reached G S ω v).mpr ⟨a,ha,hav⟩
    have hr : e ∈ ((search G S).run ω).read := by
      by_contra hn
      exact he ⟨e,hn,v,hv,hve⟩
    rw [hrd] at hr
    exact List.mem_toFinset.mp hr

lemma pair_reads (G : BondGraph V E) (a b : V) (ω : E → Bool) (e : E) :
    e ∈ (pair G a b).reads ω ↔
      ∃ v ∈ G.ends e, (G.openGraph {e | ω e = true}).Reachable a v ∨
        (G.openGraph {e | ω e = true}).Reachable b v := by
  simp only [pair,search_reads,Finset.mem_insert,Finset.mem_singleton,exists_eq_or_imp, exists_eq_left]

end CriticalPercolation.ExactExposure

namespace CriticalPercolation
namespace SearchTree
variable {E R : Type*}

lemma bare_reads (T : SearchTree E R) (ω : E → Bool) : T.bare.reads ω = T.reads ω := by
  induction T with
  | done _ => rfl
  | ask e l r hl hr => simp only [bare,QueryTree.reads,reads,hl,hr]

lemma bare_valid [DecidableEq E] (T : SearchTree E R) (used : Finset E) (h : T.Valid used) :
    T.bare.Valid used := by
  induction T generalizing used with
  | done _ => trivial
  | ask e l r hl hr => exact ⟨h.1,hl _ h.2.1,hr _ h.2.2⟩

end SearchTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteEntropy FiniteProduct

variable {V E I : Type*} [Fintype E] [Fintype I]

lemma pair_users (G : BondGraph V E) (a b : I → V) (ω : E → Bool) (e : E)
    (u v : V) (he : G.ends e = s(u,v)) :
    OrderedQuery.users (fun i => (pair G (a i) (b i)).bare) ω e =
      clusterUsers G a b ω u ∪ clusterUsers G a b ω v := by
  ext i
  simp only [OrderedQuery.mem_users,SearchTree.bare_reads,pair_reads,he,Sym2.mem_iff,
    clusterUsers,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨x,hx,hr⟩
    rcases hx with rfl | rfl
    · exact Or.inl hr
    · exact Or.inr hr
  · rintro (h | h)
    · exact ⟨u,Or.inl rfl,h⟩
    · exact ⟨v,Or.inr rfl,h⟩

lemma pair_overlap_four (G : BondGraph V E) (a b : I → V) (ω : E → Bool)
    (h : ∀ v, (clusterUsers G a b ω v).card ≤ 2) (e : E) :
    (OrderedQuery.users (fun i => (pair G (a i) (b i)).bare) ω e).card ≤ 4 := by
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective (G.ends e)
  have he' : G.ends e = s(u,v) := he.symm
  rw [pair_users G a b ω e u v he']
  exact (Finset.card_union_le _ _).trans (by have := h u; have := h v; omega)

theorem pair_entropy {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (G : BondGraph V E)
    (a b : I → V) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hm : ∑ ω, P ω = 1)
    (hc : ∀ ω, 0 < P ω → ∀ v, (clusterUsers G a b ω v).card ≤ 2) :
    (∑ i, divergence (pushMass (pair G (a i) (b i)).bare.run P)
      ((pair G (a i) (b i)).bare.reference p)) ≤
      16/(2*p*(1-p)) * divergence P (density (QueryTree.bitWeight p)) := by
  have ht (i : I) : (pair G (a i) (b i)).bare.Valid ∅ := by
    apply SearchTree.bare_valid
    exact compile_valid G _ _
  exact OrderedQuery.overlap_four_entropy hp (fun i => (pair G (a i) (b i)).bare)
    ht P hP hm (fun ω hω e => pair_overlap_four G a b ω (hc ω hω) e)

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryDescriptor
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest FiniteEntropy ExactExposure

variable {V E : Type*}

lemma descriptor_sides (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) : sides n h = fun i => (D i).1 := by
  funext i
  exact congrArg (fun D : FixedDescriptor n => (D i).1) hD

lemma sum_history_words [Fintype E] (n : ℕ) (f : History E n → ℝ) :
    (∑ h, f h) = ∑ b : Fin n → Bool, ∑ m : Fin n → Option E, f (fromWords n b m) := by
  rw [← (wordsEquiv (E := E) n).symm.sum_comp f,Fintype.sum_prod_type]
  rfl

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

lemma jointMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (z : (E → Bool) × History E n) : 0 ≤ jointMass G order d x p w s n z := by
  exact mul_nonneg (FiniteProduct.density_nonneg (fun e b => (QueryTree.bitWeight_pos hp e b).le) _)
    (density_nonneg G order d x p w _ hp h0 h1 (seed_nonneg G w _ _ s hδ) n z.2 _)

lemma fixedMass_sum (D : FixedDescriptor n) :
    (∑ z, fixedMass G order d x p w s n D z) = descriptorMass G order d x p w s n D := by
  unfold descriptorMass pushMass
  conv_rhs => rw [Fintype.sum_prod_type]
  simp_rw [sum_history_words]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  symm
  apply (Finset.sum_eq_single (fun i => (D i).1) ?_ ?_).trans
  · apply Finset.sum_congr rfl
    intro m _
    unfold fixedMass
    dsimp only
    split_ifs <;> rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro m _
    have hne : descriptor G d x n (fromWords n b m) (configuration ω) ≠ D := by
      intro he
      have hs := descriptor_sides G d x n _ _ D he
      rw [sides_fromWords] at hs
      exact hb hs
    rw [ite_eq_right hne]
  · simp

lemma conditionedMass_normalized (D : FixedDescriptor n)
    (hD : 0 < descriptorMass G order d x p w s n D) :
    ∑ z, conditionedMass G order d x p w s n D z = 1 := by
  simp only [conditionedMass,← Finset.sum_div,fixedMass_sum,div_self hD.ne']

lemma conditionedMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (D : FixedDescriptor n) (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) : 0 ≤ conditionedMass G order d x p w s n D z := by
  apply div_nonneg _ hD.le
  unfold fixedMass
  dsimp only
  split_ifs
  · exact jointMass_nonneg G order d x p w s n hp h0 h1 hδ _
  · rfl

lemma conditionedMass_support (D : FixedDescriptor n)
    (z : (E → Bool) × (Fin n → Option E))
    (hz : conditionedMass G order d x p w s n D z ≠ 0) :
    let h := fromWords n (fun i => (D i).1) z.2
    descriptor G d x n h (configuration z.1) = D ∧
    density G order d x p w (seed G w (x 0) (x d) s) n h (configuration z.1) ≠ 0 := by
  have hf := (div_ne_zero_iff.mp hz).1
  unfold fixedMass at hf
  dsimp only at hf ⊢
  split_ifs at hf with ht
  · exact ⟨ht,(mul_ne_zero_iff.mp hf).2⟩
  · exact (hf rfl).elim

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryParents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

lemma parent_eq_previous (u v a : ℕ) (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.active u v) :
    F.parent a = ((Finset.range a).filter fun b =>
      (b<2 ∨ b ∈ F.active u v) ∧ F.root b = F.root a).sup id := by
  have ha2 := (F.mem_active.mp ha).2
  apply le_antisymm
  · apply Finset.le_sup (f := id)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (F.parent_lt a ha2),
      F.active_parent ha,(F.root_step ha2).symm⟩
  · apply Finset.sup_le
    intro b hb
    obtain ⟨hba,hb,hroot⟩ := Finset.mem_filter.mp hb
    have hba' := Finset.mem_range.mp hba
    rcases hb with hb|hb
    · have hr := F.mem_lineage_le (F.root_mem_lineage (F.parent a))
      rw [← F.root_step ha2,← hroot,F.root_base hb] at hr
      exact hr
    · exact F.previous_active_le_parent huv ha hb hroot.symm hba'
end CriticalPercolation.InterpolationForest.Forest

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

lemma activeNodes_eq_descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) :
    activeNodes G d x n h ω = descriptorActive n D := by
  ext i
  constructor
  · intro hi
    have hi2 := (Forest.mem_active _).mp hi |>.2
    have hin := active_lt G d x n h ω i hi
    let j : Fin n := ⟨i-2,by omega⟩
    have hj : j.val+2=i := by dsimp [j]; omega
    refine Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hj⟩
    rw [← hD]
    simpa only [descriptor,hj,decide_eq_true_eq] using hi
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have ht := (Finset.mem_filter.mp hj).2
    rw [← hD] at ht
    simpa only [descriptor,decide_eq_true_eq] using ht

lemma node_eq_descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) (i : ℕ) :
    node d x n h i = descriptorNode (E := E) d x n D i := by
  have hs := descriptor_sides G d x n h ω D hD
  unfold node descriptorNode
  rw [anchors_sides d x n h (fromWords n (fun j => (D j).1) (fun _ => (none : Option E)))
    (hs.trans (sides_fromWords n _ _).symm)]
  rfl

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Prop)
variable (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0)

include hr in
lemma node_colour_eq_iff_root (i j : ℕ) (hi : i<n+2) (hj : j<n+2) :
    (node d x n h i).2 = (node d x n h j).2 ↔
      (historyForest G d x ω n h).root i = (historyForest G d x ω n h).root j := by
  rw [node_root_colour G order d x p w _ n h ω hr i hi,
    node_root_colour G order d x p w _ n h ω hr j hj]
  have hi2 := (historyForest G d x ω n h).root_lt_two i
  have hj2 := (historyForest G d x ω n h).root_lt_two j
  split_ifs <;> simp_all <;> omega

include hr in

theorem active_parent_eq_descriptor (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) (i : ℕ)
    (hi : i ∈ activeNodes G d x n h ω) :
    nodeParent G d x ω n h i = descriptorParent (E := E) d x n D i := by
  have ht := terminal_roots G order d x p w s n h ω hr
  have hne : (historyForest G d x ω n h).root
      (owner G d x n h ω (x (interval d n h).1)) ≠
      (historyForest G d x ω n h).root
      (owner G d x n h ω (x (interval d n h).2)) := by rw [ht.1,ht.2]; omega
  have he := (historyForest G d x ω n h).parent_eq_previous _ _ i hne hi
  change nodeParent G d x ω n h i = _ at he
  rw [he]
  unfold descriptorParent
  congr 1
  ext j
  simp only [Finset.mem_filter]
  by_cases hj : j ∈ Finset.range i
  · simp only [hj,true_and]
    have hji := Finset.mem_range.mp hj
    have hin := active_lt G d x n h ω i hi
    rw [← activeNodes_eq_descriptor G d x n h ω D hD,
      ← node_eq_descriptor G d x n h ω D hD j,← node_eq_descriptor G d x n h ω D hD i]
    exact and_congr_right fun _ => (node_colour_eq_iff_root G order d x p w s n h ω hr j i
      (hji.trans hin) hin).symm
  · simp only [hj,false_and]

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryPairs
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype I]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Bool)

theorem active_cluster_users_le
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h (configuration ω) ≠ 0)
    (idx : I → ℕ) (hinj : Function.Injective idx)
    (hidx : ∀ i, idx i ∈ activeNodes G d x n h (configuration ω)) (v : V) :
    (clusterUsers G (fun i => (node d x n h (idx i)).1)
      (fun i => (node d x n h (nodeParent G d x (configuration ω) n h (idx i))).1) ω v).card ≤ 2 := by
  classical
  let F := historyForest G d x (configuration ω) n h
  let S := activeNodes G d x n h (configuration ω)
  let users := clusterUsers G (fun i => (node d x n h (idx i)).1)
      (fun i => (node d x n h (F.parent (idx i))).1) ω v
  have hb (i : I) : 2 ≤ idx i ∧ idx i<n+2 :=
    ⟨(Forest.mem_active _).mp (hidx i) |>.2,active_lt G d x n h _ _ (hidx i)⟩
  have hcan (i : I) : Canonical G (anchors d x n h) (configuration ω) (idx i) :=
    active_canonical G order d x p w _ n h _ hr _ (hidx i)
  have hpcan (i : I) : Canonical G (anchors d x n h) (configuration ω) (F.parent (idx i)) :=
    nodeParent_canonical G order d x p w _ n h _ hr _ (hb i).1 (hb i).2
  have hpbound (i : I) : F.parent (idx i)<n+2 := (F.parent_lt _ (hb i).1).trans (hb i).2
  by_cases hu : users.Nonempty
  · obtain ⟨i,hi⟩ := hu
    have hi' := hi
    simp only [users,clusterUsers,Finset.mem_filter,Finset.mem_univ,true_and] at hi'
    obtain ⟨j,hj,hjc,hjv⟩ : ∃ j<n+2, Canonical G (anchors d x n h) (configuration ω) j ∧
        (G.openGraph (configuration ω)).Reachable (node d x n h j).1 v := by
      rcases hi' with hi'|hi'
      · exact ⟨idx i,(hb i).2,hcan i,hi'⟩
      · exact ⟨F.parent (idx i),hpbound i,hpcan i,hi'⟩
    have hm : Set.MapsTo idx (↑users : Set I) (↑(S.filter fun k => k=j ∨ F.parent k=j) : Set ℕ) := by
      intro k hk
      refine Finset.mem_filter.mpr ⟨hidx k,?_⟩
      simp only [users,clusterUsers,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hk
      rcases hk with hk|hk
      · exact Or.inl (canonical_node_reachable_eq G d x n h (configuration ω) _ j
          (hb k).2 hj (hcan k) hjc (hk.trans hjv.symm))
      · exact Or.inr (canonical_node_reachable_eq G d x n h (configuration ω) _ j
          (hpbound k) hj (hpcan k) hjc (hk.trans hjv.symm))
    have hc : users.card ≤ (S.filter fun k => k=j ∨ F.parent k=j).card :=
      Finset.card_le_card_of_injOn idx hm hinj.injOn
    have ht := terminal_roots G order d x p w s n h (configuration ω) hr
    have hne : F.root (owner G d x n h (configuration ω) (x (interval d n h).1)) ≠
        F.root (owner G d x n h (configuration ω) (x (interval d n h).2)) := by
      change (historyForest G d x (configuration ω) n h).root _ ≠ _
      rw [ht.1,ht.2]
      omega
    exact hc.trans (F.active_pair_multiplicity hne j)
  · have he : users=∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    change users.card ≤ 2
    rw [he,Finset.card_empty]
    omega

omit [Fintype I] in
lemma fixed_cluster_users_le (D : FixedDescriptor n) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (v : V) :
    (clusterUsers G (activeLeft (E := E) d x n D) (activeRight (E := E) d x n D) ω v).card ≤ 2 := by
  classical
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hi (i : ActiveIndex n D) : i.val.val+2 ∈ activeNodes G d x n h (configuration ω) := by
    rw [activeNodes_eq_descriptor G d x n h _ D hD]
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩,rfl⟩
  have hinj : Function.Injective (fun i : ActiveIndex n D => i.val.val+2) := by
    intro i j he
    apply Subtype.ext
    apply Fin.ext
    dsimp only at he
    omega
  have he := active_cluster_users_le G order d x p w s n h ω hr _ hinj hi v
  have hleft (i : ActiveIndex n D) : (node d x n h (i.val.val+2)).1 = activeLeft (E := E) d x n D i :=
    congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
  have hright (i : ActiveIndex n D) :
      (node d x n h (nodeParent G d x (configuration ω) n h (i.val.val+2))).1 =
      activeRight (E := E) d x n D i := by
    rw [active_parent_eq_descriptor G order d x p w s n h _ hr D hD _ (hi i)]
    exact congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
  simp_rw [hleft,hright] at he
  exact he

noncomputable section Entropy

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.pairsClassicalFinDecidable
omit [Fintype I] in
lemma configurationMass_support (D : FixedDescriptor n) (η : E → Bool)
    (hη : 0 < pushMass Prod.fst (conditionedMass G order d x p w s n D) η) :
    ∃ m, 0 < conditionedMass G order d x p w s n D (η,m) := by
  by_contra! hn
  have hz : pushMass Prod.fst (conditionedMass G order d x p w s n D) η ≤ 0 := by
    unfold pushMass
    apply Finset.sum_nonpos
    intro z _
    split_ifs with he
    · rcases z with ⟨η',m⟩
      dsimp only at he
      subst η'
      exact hn m
    · rfl
  linarith

omit [Fintype I] in

theorem conditioned_pair_entropy_bs_oai (D : FixedDescriptor n)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let P := pushMass Prod.fst (conditionedMass G order d x p w s n D)
    (∑ i : ActiveIndex n D,
      divergence (pushMass (pair G (activeLeft (E := E) d x n D i)
        (activeRight (E := E) d x n D i)).bare.run P)
      ((pair G (activeLeft (E := E) d x n D i) (activeRight (E := E) d x n D i)).bare.reference p)) ≤
      16/(2*p*(1-p)) * divergence P (FiniteProduct.density (QueryTree.bitWeight p)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  cases Subsingleton.elim (inferInstance : DecidableEq E) (Classical.decEq E)
  dsimp only
  let Q := conditionedMass G order d x p w s n D
  have hQ : ∀ z, 0 ≤ Q z := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z = 1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  apply pair_entropy hp G (activeLeft (E := E) d x n D) (activeRight (E := E) d x n D)
    (pushMass Prod.fst Q) (pushMass_nonneg _ _ hQ) (by rw [pushMass_sum,hQ1])
  intro η hη v
  obtain ⟨m,hm⟩ := configurationMass_support G order d x p w s n D η hη
  exact fixed_cluster_users_le G order d x p w s n η D m hm.ne' v

end Entropy
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy_bs_oai.{u_1, u_2}
