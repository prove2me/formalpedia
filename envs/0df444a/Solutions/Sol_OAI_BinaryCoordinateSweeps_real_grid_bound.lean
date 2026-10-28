-- Prove2me | solution 1 for OAI.BinaryCoordinateSweeps.real_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T16:01:55.285302+00:00
-- url     : https://prove2.me/submissions/aa0424f5-773e-4d3f-a0f3-7d6785351628

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000
import Theorems.Thm_OAI_BinaryCoordinateSweeps_dense_induction_step_eventually
import Theorems.Thm_OAI_BinaryCoordinateSweeps_sparse_uniform_radius

section
-- module Solutions.OAIB3_Bsw.Compat
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
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
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_Basic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section FiniteProbability
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

lemma finiteLaw_nonneg (f : Ω → G) (g : G) : 0 ≤ finiteLaw f g := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma finiteLaw_sum [Nonempty Ω] (f : Ω → G) : ∑ g, finiteLaw f g = 1 := by
  classical
  simp only [finiteLaw]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

lemma uniformLaw_sum [Nonempty G] : ∑ g, uniformLaw G g = 1 := by
  simp [uniformLaw, Fintype.card_ne_zero]

end FiniteProbability

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma average_compatible (p : G → ℂ) (f : IntertwiningMap ρ σ) (v : V) :
    groupAverage σ p (f v) = f (groupAverage ρ p v) := by
  simp only [groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    IntertwiningMap.isIntertwining]

lemma adjoint_average_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (f : IntertwiningMap ρ σ) (v : V) :
    (groupAverage σ p).adjoint (f v) = f ((groupAverage ρ p).adjoint v) := by
  simp only [groupAverage,map_sum,map_smulₛₗ,unitary_rep_adjoint ρ hρ,
    unitary_rep_adjoint σ hσ,LinearMap.sum_apply,LinearMap.smul_apply,
    IntertwiningMap.isIntertwining, RingHom.id_apply]

lemma even_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (q : ℕ) (f : IntertwiningMap ρ σ) (v : V) :
    (((groupAverage σ p).adjoint * groupAverage σ p)^q) (f v) =
      f ((((groupAverage ρ p).adjoint * groupAverage ρ p)^q) v) := by
  induction q generalizing v with
  | zero => simp
  | succ q ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih]
    rw [Module.End.mul_apply,average_compatible,adjoint_average_compatible ρ σ p hρ hσ]
    rfl

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_GridSweepPath
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

theorem pathEvent_nonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    ∃ g : GridChoices bits, pathEvent H g := by
  classical
  let A (j : Fin b) (y : GridOutside bits j) :=
    {k : Fin h // (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i) = y}
  have hp (j : Fin b) (y : GridOutside bits j) :
      ∃ σ : Equiv.Perm (Slot (bits j)), ∀ k : A j y,
        σ (H.position j.castSucc k.val j) = H.position j.succ k.val j := by
    apply Equiv.Perm.exists_extending_pair
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.castSucc
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.succ
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · rw [H.changes_only_stage j k.val i hi, H.changes_only_stage j l.val i hi]
        exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
  choose g hg using hp
  refine ⟨g, ?_⟩
  intro j k
  apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
  simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
  apply Prod.ext
  · exact hg j _ ⟨k, rfl⟩
  · funext i
    exact (H.changes_only_stage j k i.val i.property).symm

lemma lineLaw_pos (d : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : Equiv.Perm (Slot d)) : 0 < lineLaw d z g := by
  have hu : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    exact inv_pos.mpr hc
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hz1) hu)
    (mul_nonneg hz (finiteLaw_nonneg (binarySweep d) g))

lemma lineLaw_sum (d : ℕ) (z : ℝ) : ∑ g, lineLaw d z g = 1 := by
  simp only [lineLaw, Finset.sum_add_distrib, ← Finset.mul_sum,
    uniformLaw_sum, binaryLaw, finiteLaw_sum]
  ring

lemma gridWeight_pos {b : ℕ} (bits : Fin b → ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : GridChoices bits) : 0 < gridWeight bits z g := by
  apply Finset.prod_pos
  intro j _
  exact Finset.prod_pos (fun y _ => lineLaw_pos (bits j) hz hz1 (g j y))

lemma gridWeight_sum {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) :
    ∑ g : GridChoices bits, gridWeight bits z g = 1 := by
  classical
  unfold gridWeight
  rw [← Fintype.prod_sum (fun (j : Fin b)
    (g : GridOutside bits j → Equiv.Perm (Slot (bits j))) => ∏ y, lineLaw (bits j) z (g y))]
  have hj (j : Fin b) : ∑ g : GridOutside bits j → Equiv.Perm (Slot (bits j)),
      ∏ y, lineLaw (bits j) z (g y) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : GridOutside bits j)
      (g : Equiv.Perm (Slot (bits j))) => lineLaw (bits j) z g)]
    simp [lineLaw_sum]
  simp [hj]

theorem conditionalNormalizer_pos {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) : 0 < conditionalNormalizer H z := by
  classical
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  apply Finset.sum_pos'
  · intro g' _
    split_ifs
    · exact (gridWeight_pos bits hz hz1 g').le
    · exact le_rfl
  · exact ⟨g, Finset.mem_univ _, by simpa [hg] using gridWeight_pos bits hz hz1 g⟩

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryLineDisk
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma complexLineLaw_real (d : ℕ) (z : ℝ) (g : Equiv.Perm (Slot d)) :
    complexLineLaw d (z:ℂ) g=(lineLaw d z g:ℂ) := by
  simp [complexLineLaw,lineLaw]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_ComplexGrid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

lemma complexGridWeight_real (z : ℝ) (g : GridChoices bits) :
    complexGridWeight bits (z:ℂ) g=(gridWeight bits z g:ℂ) := by
  simp [complexGridWeight,gridWeight,complexLineLaw_real]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_SumDite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
lemma sum_dite_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : ∀ x, P x → M) :
    (∑ x, if h : P x then f x h else 0) = ∑ x : {x // P x}, f x.val x.property := by
  classical
  have he := (Equiv.Set.sumCompl {x | P x}).sum_comp
    (fun x => if h : P x then f x h else 0)
  rw [Fintype.sum_sum_type] at he
  rw [← he]
  simp only [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inr]
  have hp : (∑ x : {x // P x}, if h : P x.val then f x.val h else 0) =
      ∑ x : {x // P x}, f x.val x.property := by
    apply Finset.sum_congr rfl
    intro x _
    exact dite_eq_left x.property
  have hn : (∑ x : {x // ¬P x}, if h : P x.val then f x.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact dite_eq_right x.property
  exact (congrArg₂ (· + ·) hp hn).trans (add_zero _)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_IndependentHistory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma fallingCost_sum {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = ∑ j ∈ Finset.range u, Real.log ((m : ℝ) / (m - j : ℕ)) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hdf : (0 : ℝ) < m.descFactorial u := by exact_mod_cast (Nat.descFactorial_pos.mpr hu)
  have hdiff (j : ℕ) (hj : j ∈ Finset.range u) : (m - j : ℕ) ≠ 0 := by
    simp only [Finset.mem_range] at hj
    omega
  have hlog (j : ℕ) (hj : j ∈ Finset.range u) :
      Real.log ((m : ℝ) / (m - j : ℕ)) = Real.log m - Real.log (m - j : ℕ) :=
    Real.log_div hmp.ne' (by exact_mod_cast hdiff j hj)
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp.ne') hdf.ne', Real.log_pow,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod, Real.log_prod (fun j hj => by exact_mod_cast hdiff j hj)]
  rw [Finset.sum_congr rfl hlog, Finset.sum_sub_distrib]
  simp

lemma prefix_sum_le_of_full_sum_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) (f : ℕ → ℝ)
    (hf : ∀ i < u, ∀ j, u ≤ j → j < m → f i ≤ f j)
    (hfull : ∑ j ∈ Finset.range m, f j ≤ m) :
    ∑ j ∈ Finset.range u, f j ≤ u := by
  have hc : ((m : ℝ) - u) * (∑ i ∈ Finset.range u, f i) ≤
      (u : ℝ) * ∑ j ∈ Finset.Ico u m, f j := by
    calc
      _ = ∑ i ∈ Finset.range u, ∑ _j ∈ Finset.Ico u m, f i := by
        simp [Nat.cast_sub hu, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hf i (Finset.mem_range.mp hi) j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      _ = _ := by simp
  have hsplit := Finset.sum_range_add_sum_Ico f hu
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : (0 : ℝ) ≤ u := by positivity
  nlinarith

lemma fallingCost_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) : fallingCost m u ≤ u := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hfull : fallingCost m m ≤ m := by
    have hst := Stirling.le_log_factorial_stirling hm.ne'
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [fallingCost, Nat.descFactorial_self, Real.log_div (pow_ne_zero _ hmp.ne') (by positivity), Real.log_pow]
    linarith
  rw [fallingCost_sum hm hu]
  apply prefix_sum_le_of_full_sum_le hm hu
  · intro i hi j huj hjm
    apply Real.log_le_log
    · exact div_pos hmp (by exact_mod_cast Nat.sub_pos_of_lt (hi.trans_le hu))
    · apply div_le_div_of_nonneg_left hmp.le
      · exact_mod_cast Nat.sub_pos_of_lt hjm
      · exact_mod_cast Nat.sub_le_sub_left (hi.le.trans huj) m
  · rwa [← fallingCost_sum hm le_rfl]

attribute [local instance] Classical.propDecidable

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IrrepSupport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps
namespace Irrep

variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V) [ρ.IsIrreducible]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma invariant_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V)
    (v : V) (hv : ∀ g, ρ g v = v) : v = 0 := by
  let f : Representation.IntertwiningMap (1 : Representation ℂ G ℂ) ρ :=
    (LinearMap.toSpanSingleton ℂ V v).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g c
      simp only [MonoidHom.one_apply, Module.End.one_apply, LinearMap.toSpanSingleton_apply,
        map_smul, hv])
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hf | hf
  · have hd := LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf
    simp only [Module.finrank_self] at hd
    omega
  · have hh := congrArg (fun a : Representation.IntertwiningMap
        (1 : Representation ℂ G ℂ) ρ => a (1 : ℂ)) hf
    simpa [f] using hh

omit [FiniteDimensional ℂ V] in
lemma sum_apply_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V) (x : V) :
    ∑ g : G, ρ g x = 0 := by
  apply invariant_eq_zero_of_finrank_gt_one ρ hD
  intro g
  simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
  exact Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h : G => ρ h x)

omit [FiniteDimensional ℂ V] in
lemma sum_eq_zero_of_finrank_gt_one (hD : 1 < Module.finrank ℂ V) :
    ∑ g : G, ρ g = 0 := by
  ext x
  simpa using sum_apply_eq_zero_of_finrank_gt_one ρ hD x

include ρ in
omit [FiniteDimensional ℂ V] in
lemma finrank_le_card : Module.finrank ℂ V ≤ Fintype.card G := by
  let : IsSimpleModule ℂ[G] ρ.asModule := inferInstance
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  let f : ℂ[G] →ₗ[ℂ] ρ.asModule :=
    (LinearMap.toSpanSingleton ℂ[G] ρ.asModule v).restrictScalars ℂ
  have hf : Function.Surjective f := IsSimpleModule.toSpanSingleton_surjective ℂ[G] hv
  have hd := LinearMap.finrank_le_finrank_of_surjective (f := f) hf
  have he : Module.finrank ℂ ρ.asModule = Module.finrank ℂ V :=
    ρ.asModuleEquiv.finrank_eq
  rw [he] at hd
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ)] at hd
  exact hd

end Irrep
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_OneAxis
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma assignmentResidualEquiv_apply {X I : Type*} [Fintype X] [Fintype I]
    (A B : I ↪ X) (c : {x : X // x ∉ Set.range A} ≃ {x : X // x ∉ Set.range B})
    (σ : {σ : Equiv.Perm X // Assigns A B σ}) (x : {x : X // x ∉ Set.range A}) :
    (c (assignmentResidualEquiv A B c σ x)).val = σ.val x := by
  simp [assignmentResidualEquiv, Equiv.equivCongr, Equiv.Set.compl]
  rfl

lemma oneAxisRemainingEquiv_apply {h : ℕ} {bits : Fin 1 → ℕ} (H : PathFamily bits h)
    (g : {g : GridChoices bits // pathEvent H g}) :
    oneAxisRemainingEquiv H g = remainingPerm H g.val g.property := by
  apply Equiv.ext
  intro x
  apply (freeIdentification H).injective
  apply Subtype.ext
  have he := assignmentResidualEquiv_apply
    (⟨H.position 0, H.disjoint 0⟩ : Fin h ↪ GridSlot bits)
    (⟨H.position (Fin.last 1), H.disjoint _⟩ : Fin h ↪ GridSlot bits)
    (freeIdentification H)
    ((Equiv.subtypeEquiv (oneAxisSweepEquiv bits) (by
      intro g
      simpa only [Assigns, oneAxisSweepEquiv_apply, Function.Embedding.coeFn_mk] using oneAxis_pathEvent_iff H g)) g) x
  simpa only [oneAxisRemainingEquiv, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    oneAxisSweepEquiv_apply, remainingPerm, Equiv.apply_symm_apply, remainingBijection,
    Equiv.coe_fn_mk] using he

lemma oneAxis_gridWeight (bits : Fin 1 → ℕ) (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g = lineLaw (bits 0) z (oneAxisChoiceEquiv bits g) := by
  simp [gridWeight, oneAxisChoiceEquiv, Equiv.piUnique, Equiv.funUnique]

lemma oneAxis_gridWeight_zero (bits : Fin 1 → ℕ) (g : GridChoices bits) :
    gridWeight bits 0 g = (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ := by
  rw [oneAxis_gridWeight]
  simp only [lineLaw, sub_zero, one_mul, zero_mul, add_zero, uniformLaw]
  congr 2
  exact Fintype.card_congr (oneAxisSlotEquiv bits).symm.permCongr

lemma oneAxis_conditionalOperator_zero {h D : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hD : 1 < D) : conditionalOperator H 0 ρ = 0 := by
  have hdim : 1 < Module.finrank ℂ (RepSpace D) := by simpa using hD
  have hsum := Irrep.sum_eq_zero_of_finrank_gt_one ρ hdim
  have hperm : (∑ g : {g : GridChoices bits // pathEvent H g},
      ρ (remainingPerm H g.val g.property)) = 0 := by
    calc
      _ = ∑ g : {g : GridChoices bits // pathEvent H g}, ρ (oneAxisRemainingEquiv H g) := by
        simp only [oneAxisRemainingEquiv_apply]
      _ = 0 := ((oneAxisRemainingEquiv H).sum_comp (fun σ => ρ σ)).trans hsum
  unfold conditionalOperator
  have he : (∑ g : GridChoices bits, if hg : pathEvent H g then
      (gridWeight bits 0 g : ℂ) • ρ (remainingPerm H g hg) else 0) = 0 := by
    rw [sum_dite_zero]
    simp only [oneAxis_gridWeight_zero, ← Finset.smul_sum]
    apply smul_eq_zero.mpr
    right
    convert hperm using 1
  rw [he, smul_zero]
  rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_MomentBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma conditionalOperator_apply {b h D : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) (x : RepSpace D) :
    conditionalOperator H z ρ x = (conditionalNormalizer H z : ℂ)⁻¹ •
      ∑ g : GridChoices bits, if hg : pathEvent H g then
        (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) x else 0 := by
  classical
  unfold conditionalOperator
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> rfl

theorem conditionalOperator_norm_le_one {b h D : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    (hρ : IsUnitaryRep ρ) : ‖conditionalOperator H z ρ‖ ≤ 1 := by
  classical
  apply (conditionalOperator H z ρ).opNorm_le_bound (by norm_num)
  intro x
  rw [one_mul, conditionalOperator_apply, norm_smul]
  have hZ := conditionalNormalizer_pos H hz hz1
  have hsum : ‖∑ g : GridChoices bits, if hg : pathEvent H g then
      (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) x else 0‖ ≤
      conditionalNormalizer H z * ‖x‖ := by
    calc
      _ ≤ ∑ g : GridChoices bits, ‖if hg : pathEvent H g then
        (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) x else 0‖ := norm_sum_le _ _
      _ = _ := by
        unfold conditionalNormalizer
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        by_cases hg : pathEvent H g
        · simp only [dite_eq_left hg, ite_eq_left hg, norm_smul, hρ (remainingPerm H g hg) x,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gridWeight_pos bits hz hz1 g)]
        · simp only [dite_eq_right hg, ite_eq_right hg, norm_zero, zero_mul]
  calc
    _ ≤ ‖(conditionalNormalizer H z : ℂ)⁻¹‖ * (conditionalNormalizer H z * ‖x‖) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖x‖ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ,
        ← mul_assoc, inv_mul_cancel₀ hZ.ne', one_mul]

theorem traceMoment_le_dimension {D : ℕ} (q : ℕ) (K : RepSpace D →L[ℂ] RepSpace D)
    (hK : ‖K‖ ≤ 1) : traceMoment q K ≤ D := by
  let B := ((ContinuousLinearMap.adjoint K) * K) ^ q
  have hB : ‖B‖ ≤ 1 := by
    cases q with
    | zero => exact ContinuousLinearMap.norm_id_le
    | succ q =>
      change ‖((ContinuousLinearMap.adjoint K) * K) ^ (q+1)‖ ≤ 1
      calc
        _ ≤ ‖(ContinuousLinearMap.adjoint K) * K‖ ^ (q+1) := norm_pow_le' _ (by omega)
        _ ≤ 1 ^ (q+1) := by
          gcongr
          calc
            _ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖K‖ := norm_mul_le _ _
            _ = ‖K‖ * ‖K‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
            _ ≤ 1 * 1 := mul_le_mul hK hK (norm_nonneg _) (by norm_num)
            _ = 1 := one_mul _
        _ = 1 := one_pow _
  unfold traceMoment
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin D) ℂ), Complex.re_sum]
  calc
    _ ≤ ∑ _i : Fin D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hb : ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ = 1 :=
        (EuclideanSpace.basisFun (Fin D) ℂ).orthonormal.1 i
      calc
        _ ≤ ‖inner ℂ (EuclideanSpace.basisFun (Fin D) ℂ i)
            (B (EuclideanSpace.basisFun (Fin D) ℂ i))‖ := Complex.re_le_norm _
        _ ≤ ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ *
            ‖B (EuclideanSpace.basisFun (Fin D) ℂ i)‖ := norm_inner_le_norm _ _
        _ ≤ 1 := by
          rw [hb, one_mul]
          exact (B.le_opNorm _).trans (by rw [hb, mul_one]; exact hB)
    _ = _ := by simp

lemma logMoment_traceMoment_le_log_dimension {D : ℕ} (q : ℕ)
    (K : RepSpace D →L[ℂ] RepSpace D) (hK : ‖K‖ ≤ 1) :
    logMoment (traceMoment q K) ≤ (Real.log D : EReal) := by
  have ht := traceMoment_le_dimension q K hK
  unfold logMoment
  cases D with
  | zero =>
    have he : ENNReal.ofReal (traceMoment q K) = 0 := ENNReal.ofReal_eq_zero.mpr (by simpa only [Nat.cast_zero] using ht)
    rw [he, ENNReal.log_zero]
    exact bot_le
  | succ D =>
    have hp : (0 : ℝ) < D+1 := by positivity
    have he := ENNReal.log_le_log (ENNReal.ofReal_le_ofReal ht)
    simpa only [Nat.cast_add, Nat.cast_one, ENNReal.log_ofReal_of_pos hp] using he

theorem conditional_moment_of_automatic_regime {b h D : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (q : ℕ) (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    (hρ : IsUnitaryRep ρ)
    (ha : (1 + cExponent (gridSize bits)) * Real.log D ≤
      eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H) :
    logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
      ((-cExponent (gridSize bits) * Real.log D +
        eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H : ℝ) : EReal) := by
  apply (logMoment_traceMoment_le_log_dimension q _
    (conditionalOperator_norm_le_one H hz hz1 ρ hρ)).trans
  exact_mod_cast (show Real.log D ≤ -cExponent (gridSize bits) * Real.log D +
    eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H by linarith)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_OneAxisPerturbation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma oneAxis_gridWeight_affine (bits : Fin 1 → ℕ) (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g = (1-z)*gridWeight bits 0 g + z*gridWeight bits 1 g := by
  simp only [oneAxis_gridWeight, lineLaw]
  ring

lemma oneAxis_gridWeight_one_nonneg (bits : Fin 1 → ℕ) (g : GridChoices bits) :
    0 ≤ gridWeight bits 1 g := by
  simp only [oneAxis_gridWeight, lineLaw, sub_self, zero_mul, one_mul, zero_add]
  exact finiteLaw_nonneg (binarySweep _) _

lemma oneAxis_conditional_norm_le_z_div {h D : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) (hD : 1 < D) :
    ‖conditionalOperator H z ρ‖ ≤ z / conditionalNormalizer H z := by
  have hZ := conditionalNormalizer_pos H hz hz1
  apply (conditionalOperator H z ρ).opNorm_le_bound (div_nonneg hz hZ.le)
  intro x
  let F (w : ℝ) : RepSpace D := ∑ g : GridChoices bits, if hg : pathEvent H g then
    (gridWeight bits w g : ℂ) • ρ (remainingPerm H g hg) x else 0
  have hF0 : F 0 = 0 := by
    have he := congrArg (fun K : RepSpace D →L[ℂ] RepSpace D => K x)
      (oneAxis_conditionalOperator_zero H ρ hD)
    rw [conditionalOperator_apply] at he
    change (conditionalNormalizer H 0 : ℂ)⁻¹ • F 0 = 0 at he
    exact (smul_eq_zero.mp he).resolve_left (inv_ne_zero (by
      exact_mod_cast (conditionalNormalizer_pos H (by norm_num : (0 : ℝ) ≤ 0)
        (by norm_num : (0 : ℝ) < 1)).ne'))
  have hFz : F z = (z : ℂ) • F 1 := by
    have hl : F z = ((1-z : ℝ) : ℂ) • F 0 + (z : ℂ) • F 1 := by
      simp only [F, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : pathEvent H g
      · simp only [dite_eq_left hg, oneAxis_gridWeight_affine bits z g,
          Complex.ofReal_add, Complex.ofReal_mul, add_smul, mul_smul]
      · simp only [dite_eq_right hg, smul_zero, add_zero]
    simpa only [hF0, smul_zero, zero_add] using hl
  have hF1 : ‖F 1‖ ≤ ‖x‖ := by
    calc
      _ ≤ ∑ g : GridChoices bits, ‖if hg : pathEvent H g then
        (gridWeight bits 1 g : ℂ) • ρ (remainingPerm H g hg) x else 0‖ := norm_sum_le _ _
      _ ≤ ∑ g : GridChoices bits, gridWeight bits 1 g * ‖x‖ := by
        apply Finset.sum_le_sum
        intro g _
        by_cases hg : pathEvent H g
        · simp only [dite_eq_left hg, norm_smul, hρ (remainingPerm H g hg) x, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (oneAxis_gridWeight_one_nonneg bits g), le_refl]
        · simp only [dite_eq_right hg, norm_zero]
          exact mul_nonneg (oneAxis_gridWeight_one_nonneg bits g) (norm_nonneg _)
      _ = ‖x‖ := by rw [← Finset.sum_mul, gridWeight_sum, one_mul]
  rw [conditionalOperator_apply]
  change ‖(conditionalNormalizer H z : ℂ)⁻¹ • F z‖ ≤ _
  rw [hFz, norm_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hZ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
  calc
    _ ≤ (conditionalNormalizer H z)⁻¹ * (z * ‖x‖) := by gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

lemma oneAxis_normalizer_lower {h : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1/2) :
    (2 * ((gridSize bits).factorial : ℝ))⁻¹ ≤ conditionalNormalizer H z := by
  have hz1 : z < 1 := by linarith
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  have hu : (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ =
      ((gridSize bits).factorial : ℝ)⁻¹ := by rw [Fintype.card_perm, card_gridSlot]
  calc
    _ = (1/2 : ℝ) * (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ := by
      rw [hu, mul_inv_rev]; ring
    _ ≤ gridWeight bits z g := by
      rw [oneAxis_gridWeight_affine, oneAxis_gridWeight_zero]
      have hp := mul_nonneg hz (oneAxis_gridWeight_one_nonneg bits g)
      have hn : 0 ≤ (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ := by positivity
      nlinarith
    _ ≤ conditionalNormalizer H z := by
      unfold conditionalNormalizer
      have he := Finset.single_le_sum (fun (g' : GridChoices bits) _ =>
        show 0 ≤ if pathEvent H g' then gridWeight bits z g' else 0 by
          split_ifs <;> first | exact (gridWeight_pos bits hz hz1 g').le | exact le_rfl)
        (Finset.mem_univ g)
      simpa only [ite_eq_left hg] using he

theorem oneAxis_conditional_norm_le {h D : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1/2)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) (hD : 1 < D) :
    ‖conditionalOperator H z ρ‖ ≤ 2 * ((gridSize bits).factorial : ℝ) * z := by
  have hz1 : z < 1 := by linarith
  have hb := oneAxis_normalizer_lower H hz hzhalf
  have hF : (0 : ℝ) < 2 * ((gridSize bits).factorial : ℝ) := by positivity
  calc
    _ ≤ z / conditionalNormalizer H z := oneAxis_conditional_norm_le_z_div H hz hz1 ρ hρ hD
    _ ≤ z / (2 * ((gridSize bits).factorial : ℝ))⁻¹ :=
      div_le_div_of_nonneg_left hz (inv_pos.mpr hF) hb
    _ = _ := by rw [div_inv_eq_mul]; ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_AssignmentWeight
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

attribute [local instance] Classical.propDecidable

lemma lineHoles_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : lineHoles H j y ≤ 2 ^ bits j := by
  simpa [lineHoles, Slot, Fintype.card_pi] using
    Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective

lemma sum_lineHoles {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) : ∑ y, lineHoles H j y = h := by
  classical
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun k : Fin h => (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i)))
  simpa only [Fintype.card_sigma, Fintype.card_fin, lineHoles] using hh

lemma pathCost_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H ≤ (b : ℝ) * h := by
  calc
    pathCost H ≤ ∑ j : Fin b, ∑ y, (lineHoles H j y : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro y _
      exact fallingCost_le (by positivity) (lineHoles_le H j y)
    _ = _ := by simp only [← Nat.cast_sum, sum_lineHoles]; simp

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_Placement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

instance conditionalChoicesNonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    Nonempty (ConditionalChoices H) := by
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  exact ⟨⟨g, hg⟩⟩

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathExtension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma log_gridSize {b : ℕ} (bits : Fin b → ℕ) :
    Real.log (gridSize bits : ℝ) = ∑ j, Real.log (2^bits j : ℕ) := by
  unfold gridSize
  rw [Nat.cast_prod, Real.log_prod]
  intro j _
  positivity

lemma gridSize_pos {b : ℕ} (bits : Fin b → ℕ) : 0 < gridSize bits := by
  unfold gridSize
  exact Finset.prod_pos (fun j _ => Nat.pow_pos (by norm_num))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_MainEasyCases
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma grid_log_lower {b r : ℕ} {bits : Fin b → ℕ} (hd : ∀ j, r ≤ bits j) :
    (b : ℝ) * ((r : ℝ) * Real.log 2) ≤ Real.log (gridSize bits) := by
  calc
    _ = ∑ _j : Fin b, (r : ℝ) * Real.log 2 := by simp
    _ ≤ ∑ j : Fin b, (bits j : ℝ) * Real.log 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hd j)
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    _ = _ := by
      rw [log_gridSize]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

lemma grid_parameter_allowance {b h r : ℕ} {bits : Fin b → ℕ}
    (hb : 1 ≤ b) (hd : ∀ j, r ≤ bits j)
    (hr : (400000000 : ℝ) ≤ (r : ℝ) * Real.log 2) (H : PathFamily bits h) :
    cExponent (gridSize bits) ≤ 2*c0 ∧
    e0/2 ≤ eExponent (gridSize bits) ∧
    (e0/4) * h * Real.log (gridSize bits) ≤
      eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H := by
  have hlogb := grid_log_lower hd
  have hbc : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbn : (0 : ℝ) ≤ b := by positivity
  have hm := mul_le_mul_of_nonneg_left hr hbn
  have hbl : (400000000 : ℝ) * b ≤ Real.log (gridSize bits) := by nlinarith
  have hl : (400000000 : ℝ) ≤ Real.log (gridSize bits) := by nlinarith
  have hs : (20000 : ℝ) ≤ Real.sqrt (Real.log (gridSize bits)) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact hl
  have hs' : 1 / Real.sqrt (Real.log (gridSize bits)) ≤ (1 / 20000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hs
  have hc : cExponent (gridSize bits) ≤ 2*c0 := by
    unfold cExponent c0
    linarith
  have he : e0/2 ≤ eExponent (gridSize bits) := by
    unfold eExponent e0
    linarith
  refine ⟨hc, he, ?_⟩
  have hh : (0 : ℝ) ≤ h := by positivity
  have hl0 : 0 ≤ Real.log (gridSize bits) := by linarith
  have he' := mul_le_mul_of_nonneg_right he (mul_nonneg hh hl0)
  have hbb : (b : ℝ) ≤ (e0/4) * Real.log (gridSize bits) := by
    unfold e0
    nlinarith
  have hcost := (pathCost_le H).trans (mul_le_mul_of_nonneg_right hbb hh)
  nlinarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_QuantitativeMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma traceMoment_le_dimension_mul_pow {D q : ℕ} (hq : 0 < q)
    (K : RepSpace D →L[ℂ] RepSpace D) {η : ℝ} (hη : 0 ≤ η) (hK : ‖K‖ ≤ η) :
    traceMoment q K ≤ D * η ^ (2*q) := by
  let B := ((ContinuousLinearMap.adjoint K) * K) ^ q
  have hKK : ‖(ContinuousLinearMap.adjoint K) * K‖ ≤ η^2 := by
    calc
      _ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖K‖ := norm_mul_le _ _
      _ = ‖K‖ * ‖K‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ η * η := mul_le_mul hK hK (norm_nonneg _) hη
      _ = _ := (sq η).symm
  have hB : ‖B‖ ≤ η ^ (2*q) := by
    calc
      _ ≤ ‖(ContinuousLinearMap.adjoint K) * K‖^q := norm_pow_le' _ hq
      _ ≤ (η^2)^q := pow_le_pow_left₀ (norm_nonneg _) hKK q
      _ = _ := (pow_mul η 2 q).symm
  unfold traceMoment
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin D) ℂ), Complex.re_sum]
  calc
    _ ≤ ∑ _i : Fin D, η^(2*q) := by
      apply Finset.sum_le_sum
      intro i _
      have hb : ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ = 1 :=
        (EuclideanSpace.basisFun (Fin D) ℂ).orthonormal.1 i
      calc
        _ ≤ ‖inner ℂ (EuclideanSpace.basisFun (Fin D) ℂ i)
            (B (EuclideanSpace.basisFun (Fin D) ℂ i))‖ := Complex.re_le_norm _
        _ ≤ ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ *
            ‖B (EuclideanSpace.basisFun (Fin D) ℂ i)‖ := norm_inner_le_norm _ _
        _ ≤ η^(2*q) := by
          rw [hb, one_mul]
          exact (B.le_opNorm _).trans (by rw [hb, mul_one]; exact hB)
    _ = _ := by simp

lemma logMoment_le_neg_log_dimension {D q : ℕ} (hD : 0 < D) (hq : 0 < q)
    (K : RepSpace D →L[ℂ] RepSpace D) (hK : ‖K‖ ≤ (D : ℝ)⁻¹) :
    logMoment (traceMoment q K) ≤ (-Real.log D : EReal) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hi0 : 0 ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr hD0.le
  have hi1 : (D : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hD0).mpr hD1
  have hm := traceMoment_le_dimension_mul_pow hq K hi0 hK
  have ht : traceMoment q K ≤ (D : ℝ)⁻¹ := by
    calc
      _ ≤ D * ((D : ℝ)⁻¹)^(2*q) := hm
      _ ≤ D * ((D : ℝ)⁻¹)^2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hi0 hi1 (by omega)) hD0.le
      _ = _ := by field_simp
  have he := ENNReal.log_le_log (ENNReal.ofReal_le_ofReal ht)
  simpa only [logMoment, ENNReal.log_ofReal_of_pos (inv_pos.mpr hD0), Real.log_inv, EReal.coe_neg] using he

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_OneAxisBase
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma oneAxisRadius_pos (r : ℕ) : 0 < oneAxisRadius r := by
  unfold oneAxisRadius
  positivity

lemma oneAxisRadius_le_half (r : ℕ) : oneAxisRadius r ≤ 1/2 := by
  have hB : (1 : ℝ) ≤ ((2^(2*r) : ℕ).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2^(2*r))
  unfold oneAxisRadius
  calc
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith)
    _ = 1/2 := by norm_num

lemma oneAxis_size_le {r : ℕ} {bits : Fin 1 → ℕ} (hd : ∀ j, bits j ≤ 2*r) :
    gridSize bits ≤ 2^(2*r) := by
  simp only [gridSize, Fin.prod_univ_one]
  exact Nat.pow_le_pow_right (by omega) (hd 0)

lemma oneAxis_norm_le_inv_dimension {r h D : ℕ} {bits : Fin 1 → ℕ}
    (hd : ∀ j, bits j ≤ 2*r) (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hzr : z ≤ oneAxisRadius r)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) (hD : 1 < D) :
    ‖conditionalOperator H z ρ‖ ≤ (D : ℝ)⁻¹ := by
  let B : ℝ := ((2^(2*r) : ℕ).factorial : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hfac : ((gridSize bits).factorial : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast Nat.factorial_le (oneAxis_size_le hd)
  have hdim : D ≤ (gridSize bits).factorial := by
    have hbound := Irrep.finrank_le_card ρ
    simp only [finrank_euclideanSpace_fin, Fintype.card_perm, card_freeSlot] at hbound
    exact hbound.trans (Nat.factorial_le (Nat.sub_le _ _))
  have hDB : (D : ℝ) ≤ B := (by exact_mod_cast hdim :
    (D : ℝ) ≤ ((gridSize bits).factorial : ℝ)).trans hfac
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  calc
    _ ≤ 2 * ((gridSize bits).factorial : ℝ) * z :=
      oneAxis_conditional_norm_le H hz (hzr.trans (oneAxisRadius_le_half r)) ρ hρ hD
    _ ≤ 2 * B * oneAxisRadius r := by gcongr
    _ = B⁻¹ := by dsimp [oneAxisRadius, B]; field_simp
    _ ≤ (D : ℝ)⁻¹ := inv_anti₀ hD0 hDB

theorem conditional_moment_one_axis {r q : ℕ}
    (hr : (400000000 : ℝ) ≤ (r : ℝ) * Real.log 2) (hq : 0 < q)
    (bits : Fin 1 → ℕ) (hd : ∀ j, r ≤ bits j ∧ bits j ≤ 2*r)
    {h D : ℕ} (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z)
    (hzr : z ≤ oneAxisRadius r)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) :
    logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
      ((-cExponent (gridSize bits) * Real.log D +
        eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H : ℝ) : EReal) := by
  have ha := grid_parameter_allowance (by omega : 1 ≤ 1) (fun j => (hd j).1) hr H
  have hl0 : 0 ≤ Real.log (gridSize bits) := Real.log_nonneg (by
    exact_mod_cast gridSize_pos bits)
  have hallow : 0 ≤ eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H := by
    apply le_trans _ ha.2.2
    unfold e0
    positivity
  by_cases hD : 1 < D
  · have hn := oneAxis_norm_le_inv_dimension (fun j => (hd j).2) H hz hzr ρ hρ hD
    apply (logMoment_le_neg_log_dimension (by omega) hq _ hn).trans
    have hc : cExponent (gridSize bits) ≤ 1 := by
      have := ha.1
      unfold c0 at this
      linarith
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))
    exact_mod_cast (show -Real.log D ≤ -cExponent (gridSize bits) * Real.log D +
      eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H by nlinarith)
  · have hlog : Real.log D = 0 := by
      have hD' : D = 0 ∨ D = 1 := by omega
      rcases hD' with rfl | rfl <;> norm_num
    apply conditional_moment_of_automatic_regime H hz
      (lt_of_le_of_lt (hzr.trans (oneAxisRadius_le_half r)) (by norm_num)) q ρ hρ
    simpa only [hlog, mul_zero] using hallow

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ConditionalAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (z : ℝ)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma groupAverage_conditional (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) :
    groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ)) =
      ∑ g : ConditionalChoices H, (conditionalChoiceWeight H z g : ℂ) •
        ρ (remainingPerm H g.val g.property) := by
  simp only [groupAverage,conditionalGroupLaw,Complex.ofReal_sum,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [apply_ite,Complex.ofReal_zero,ite_smul,zero_smul]
  simp

omit [FiniteDimensional ℂ V] in
lemma groupAverage_conditional_grid (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) :
    groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ)) =
      (conditionalNormalizer H z : ℂ)⁻¹ • ∑ g : GridChoices bits,
        if hg : pathEvent H g then (gridWeight bits z g : ℂ) •
          ρ (remainingPerm H g hg) else 0 := by
  rw [groupAverage_conditional]
  have hs : ∀ g : ConditionalChoices H,
      (conditionalChoiceWeight H z g : ℂ) • ρ (remainingPerm H g.val g.property) =
      (conditionalNormalizer H z : ℂ)⁻¹ •
        ((gridWeight bits z g.val : ℂ) • ρ (remainingPerm H g.val g.property)) := by
    intro g
    rw [conditionalChoiceWeight, Complex.ofReal_div, div_eq_mul_inv, mul_comm, mul_smul]
  simp_rw [hs]
  rw [← Finset.smul_sum]
  congr 1
  let F : GridChoices bits → (V →ₗ[ℂ] V) := fun g =>
    if hg : pathEvent H g then (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) else 0
  have hF : ∑ g : ConditionalChoices H, F g.val = ∑ g, F g := by
    rw [← Finset.sum_filter_of_ne (p := pathEvent H) (f := F) (by
      intro g _ hg
      by_contra hn
      simp [F,hn] at hg)]
    exact (Finset.sum_subtype _ (by simp) _).symm
  simpa only [F,dite_eq_left (Subtype.property _)] using hF

lemma conditionalOperator_groupAverage {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) :
    (conditionalOperator H z ρ).toLinearMap =
      groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ)) := by
  rw [groupAverage_conditional_grid]
  rfl

lemma conditionalMoment_evenMoment {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) (q : ℕ) :
    traceMoment q (conditionalOperator H z ρ) =
      evenMoment q (groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ))) := by
  rw [← conditionalOperator_groupAverage]
  simp only [traceMoment,evenMoment,ContinuousLinearMap.toLinearMap_pow,
    ContinuousLinearMap.toLinearMap_mul,ContinuousLinearMap.adjoint_toLinearMap]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_UnitaryTransport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

section Algebra
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

lemma irreducible_equiv (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : ρ.Equiv σ) [ρ.IsIrreducible] : σ.IsIrreducible := by
  apply (irreducible_iff_isSimpleModule_asModule σ).mpr
  exact IsSimpleModule.congr (LinearEquiv.ofBijective
    (IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) e.toLinearEquiv.bijective).symm

end Algebra
variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

lemma equivalent_evenMoment (e : ρ.Equiv σ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (p : G → ℂ) (q : ℕ) :
    evenMoment q (groupAverage ρ p) = evenMoment q (groupAverage σ p) := by
  have he : e.toLinearEquiv.conj (((groupAverage ρ p).adjoint * groupAverage ρ p)^q) =
      ((groupAverage σ p).adjoint * groupAverage σ p)^q := by
    ext w
    obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
    simp only [LinearEquiv.conj_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact (even_compatible ρ σ p hρ hσ q e.toIntertwiningMap v).symm
  unfold evenMoment
  rw [← he,LinearMap.trace_conj']

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFactor
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instDecidableEqElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.instMulActionGElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma nat_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < n := by omega
    have hl := hf (show (⟨i, hi'⟩ : Fin n) < ⟨i+1, hi⟩ from by simp)
    have hp := ih hi'
    change i ≤ f ⟨i, hi'⟩ at hp
    change i + 1 ≤ f ⟨i+1, hi⟩
    omega

lemma sum_orderEmb (s : Finset ℕ) :
    ∑ i : Fin s.card, s.orderEmbOfFin rfl i = ∑ i ∈ s, i := by
  have h := Finset.sum_map (s := (Finset.univ : Finset (Fin s.card)))
    (s.orderEmbOfFin rfl).toEmbedding (fun i : ℕ => i)
  rw [s.map_orderEmbOfFin_univ rfl] at h
  exact h.symm

lemma range_sum_le (s : Finset ℕ) :
    ∑ i ∈ Finset.range s.card, i ≤ ∑ i ∈ s, i := by
  let e := s.orderEmbOfFin rfl
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => nat_le_strictMono e e.strictMono i)
  simpa only [← Fin.sum_univ_eq_sum_range, e, sum_orderEmb] using h

lemma eq_range_of_sum_eq (s : Finset ℕ)
    (h : ∑ i ∈ s, i = ∑ i ∈ Finset.range s.card, i) : s = Finset.range s.card := by
  let e := s.orderEmbOfFin rfl
  have he : ∀ i : Fin s.card, e i = i.val := by
    have hsum : ∑ i : Fin s.card, i.val = ∑ i : Fin s.card, e i := by
      dsimp only [e]
      rw [sum_orderEmb, Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
      exact h.symm
    have hh := (Finset.sum_eq_sum_iff_of_le
        (fun (i : Fin s.card) _ => nat_le_strictMono e e.strictMono i)).mp hsum
    exact fun i => (hh i (Finset.mem_univ i)).symm
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := (s.range_orderEmbOfFin rfl ▸ hi : i ∈ Set.range e)
    rw [← hj, he]
    exact Finset.mem_range.mpr j.isLt
  · intro hi
    let j : Fin s.card := ⟨i, Finset.mem_range.mp hi⟩
    rw [← show e j = i from he j]
    exact s.orderEmbOfFin_mem rfl j

lemma mem_columnCells {μ : YoungDiagram} {j : ℕ} {x : Cell μ} :
    x ∈ columnCells μ j ↔ col x = j := by simp [columnCells]

lemma row_injectiveOn_column (μ : YoungDiagram) (j : ℕ) :
    Set.InjOn (row (μ := μ)) (↑(columnCells μ j) : Set (Cell μ)) := by
  intro x hx y hy hxy
  apply Subtype.ext
  apply Prod.ext hxy
  exact (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm

lemma image_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).image row = Finset.range (μ.colLen j) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc := x.property
    have hj := mem_columnCells.mp hx
    change x.val.2 = j at hj
    rw [← hj]
    exact YoungDiagram.mem_iff_lt_colLen.mp hc
  · intro hi
    refine ⟨⟨(i,j), YoungDiagram.mem_iff_lt_colLen.mpr hi⟩, ?_, rfl⟩
    exact mem_columnCells.mpr rfl

lemma card_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).card = μ.colLen j := by
  rw [← Finset.card_image_of_injOn (row_injectiveOn_column μ j), image_row_columnCells]
  exact Finset.card_range _

lemma sum_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    ∑ x ∈ columnCells μ j, row x = ∑ i ∈ Finset.range (μ.colLen j), i := by
  rw [← image_row_columnCells μ j]
  exact (Finset.sum_image (f := fun i : ℕ => i) (row_injectiveOn_column μ j)).symm

lemma sum_columnCells_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ∑ x ∈ columnCells μ j, row x ≤ ∑ x ∈ columnCells μ j, f x := by
  have h := range_sum_le ((columnCells μ j).image f)
  rw [Finset.card_image_of_injOn hf, card_columnCells, Finset.sum_image hf] at h
  rwa [sum_row_columnCells]

lemma column_image_of_total_sum (μ : YoungDiagram) (f : Cell μ → ℕ)
    (hf : ∀ j, Set.InjOn f (columnCells μ j))
    (hsum : ∑ x, f x = ∑ x : Cell μ, row x) (j : ℕ) :
    (columnCells μ j).image f = Finset.range (μ.colLen j) := by
  classical
  let J := (Finset.univ : Finset (Cell μ)).image col
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Cell μ)), col x ∈ J := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hfib (g : Cell μ → ℕ) :
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, g x = ∑ x, g x :=
    Finset.sum_fiberwise_of_maps_to hmaps g
  have heq : ∑ j ∈ J, ∑ x ∈ columnCells μ j, row x =
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, f x := by rw [hfib, hfib, hsum]
  have hone := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ J) => sum_columnCells_le μ f j (hf j))).mp heq
  by_cases hj : j ∈ J
  · have hc : ((columnCells μ j).image f).card = μ.colLen j := by
      rw [Finset.card_image_of_injOn (hf j), card_columnCells]
    have h : ∑ i ∈ (columnCells μ j).image f, i =
        ∑ i ∈ Finset.range ((columnCells μ j).image f).card, i := by
      rw [hc, Finset.sum_image (hf j), ← sum_row_columnCells]
      exact (hone j hj).symm
    simpa only [hc] using eq_range_of_sum_eq _ h
  · have hc : columnCells μ j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hj
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, mem_columnCells.mp hx⟩
    have hz : μ.colLen j = 0 := by rw [← card_columnCells, hc]; rfl
    simp [hc, hz]

lemma rearranged_row_mem (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) (x : Cell μ) :
    (row (π x), col x) ∈ μ := by
  have he := column_image_of_total_sum μ (fun x => row (π x)) hc
    (Equiv.sum_comp π row) (col x)
  have hm : row (π x) ∈ (columnCells μ (col x)).image (fun x => row (π x)) :=
    Finset.mem_image.mpr ⟨x, mem_columnCells.mpr rfl, rfl⟩
  rw [he, Finset.mem_range] at hm
  exact YoungDiagram.mem_iff_lt_colLen.mpr hm

lemma row_col_intersection (μ : YoungDiagram) :
    rowStabilizer μ ⊓ colStabilizer μ = ⊥ := by
  apply le_antisymm
  · intro π hπ
    change π = 1
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (hπ.1 x) (hπ.2 x)
  · exact bot_le

theorem row_col_factorization (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) :
    ∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c := by
  let t : Cell μ → Cell μ := fun x =>
    ⟨(row (π x), col x), rearranged_row_mem μ π hc x⟩
  have ht : Function.Injective t := by
    intro x y hxy
    have hcol := congrArg (fun z : Cell μ => col z) hxy
    change col x = col y at hcol
    have hrow := congrArg (fun z : Cell μ => row z) hxy
    change row (π x) = row (π y) at hrow
    exact hc (col x) (mem_columnCells.mpr rfl) (mem_columnCells.mpr hcol.symm) hrow
  let c : Equiv.Perm (Cell μ) := Equiv.ofBijective t
    ⟨ht, (Finite.injective_iff_surjective).mp ht⟩
  have cc : c ∈ colStabilizer μ := by intro x; rfl
  have cr : ∀ x, row (c x) = row (π x) := by intro x; rfl
  refine ⟨π * c⁻¹, ?_, c, cc, ?_⟩
  · intro x
    change row (π (c⁻¹ x)) = row x
    rw [← cr]
    simp
  · simp

theorem row_col_alternative (μ : YoungDiagram) (π : Equiv.Perm (Cell μ)) :
    (∃ x y : Cell μ, x ≠ y ∧ col x = col y ∧ row (π x) = row (π y)) ∨
    (∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c) := by
  by_cases hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)
  · exact Or.inr (row_col_factorization μ π hc)
  · left
    simp only [Set.InjOn] at hc
    push Not at hc
    obtain ⟨j, x, hx, y, hy, hrow, hne⟩ := hc
    exact ⟨x, y, hne, (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm, hrow⟩

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTabloid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma tabloidOfPerm_row_mul (π : G μ) (r : rowStabilizer μ) :
    tabloidOfPerm μ (π * r.val) = tabloidOfPerm μ π := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  simp

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungAnti
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma signC_swap {x y : Cell μ} (h : x ≠ y) : signC μ (Equiv.swap x y) = -1 := by
  simp [signC_eq, Equiv.Perm.sign_swap h]

lemma columnAnti_apply (v : Tabloid μ → ℂ) :
    columnAnti μ v = ∑ c : C μ, signC μ c.val • tabloidRepresentation μ c.val v := by
  simp [columnAnti, LinearMap.sum_apply]

lemma columnAnti_rep (c : C μ) (v : Tabloid μ → ℂ) :
    columnAnti μ (tabloidRepresentation μ c.val v) = signC μ c.val • columnAnti μ v := by
  rw [columnAnti_apply, columnAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val • (signC μ d.val • tabloidRepresentation μ d.val v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation μ d.val (tabloidRepresentation μ c.val v) =
    signC μ c.val • (signC μ (d * c).val • tabloidRepresentation μ (d * c).val v)
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

lemma columnAnti_basis_column (c : C μ) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ c.val)) = signC μ c.val • polytabloid μ := by
  rw [← mul_one c.val, ← smul_tabloidOfPerm, ← rep_basis, columnAnti_rep]
  rfl

lemma col_fixes_base_iff (c : C μ) :
    c.val • tabloidOfPerm μ 1 = tabloidOfPerm μ 1 ↔ c = 1 := by
  rw [smul_tabloidOfPerm, mul_one, tabloidOfPerm_eq_iff]
  constructor
  · intro hc
    have hr : c.val ∈ rowStabilizer μ := by
      have h := (rowStabilizer μ).inv_mem hc
      simpa using h
    have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hr, c.property⟩
    rw [row_col_intersection] at hi
    exact Subtype.ext hi
  · intro hc
    subst c
    simp

lemma polytabloid_base : polytabloid μ (tabloidOfPerm μ 1) = 1 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ 1 = tabloidOfPerm μ c.val ↔ c = 1 := by
    simpa [smul_tabloidOfPerm, eq_comm] using (col_fixes_base_iff μ c)
  simp only [he]
  simp

lemma polytabloid_ne_zero : polytabloid μ ≠ 0 := by
  intro h
  have hh := congrFun h (tabloidOfPerm μ 1)
  rw [polytabloid_base] at hh
  exact one_ne_zero hh

lemma swap_mem_fiber {X Y : Type*} [DecidableEq X] (f : X → Y) {x y : X}
    (h : f x = f y) : Equiv.swap x y ∈ fiberStabilizer f := by
  intro z
  exact Equiv.apply_swap_eq_self h z

lemma swap_fixes_tabloid (t : Tabloid μ) {x y : Cell μ} (h : t.val x = t.val y) :
    (Equiv.swap x y : G μ) • t = t := by
  apply Subtype.ext
  funext z
  change t.val ((Equiv.swap x y)⁻¹ z) = t.val z
  simpa only [Equiv.swap_inv] using Equiv.apply_swap_eq_self h z

lemma columnAnti_basis_collision (π : G μ) {x y : Cell μ}
    (hne : x ≠ y) (hc : col x = col y) (hr : row (π⁻¹ x) = row (π⁻¹ y)) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have hf : c.val • tabloidOfPerm μ π = tabloidOfPerm μ π :=
    swap_fixes_tabloid μ _ hr
  have h := columnAnti_rep μ c (tabloidBasis μ (tabloidOfPerm μ π))
  rw [rep_basis, hf] at h
  have hs : signC μ c.val = -1 := signC_swap μ hne
  rw [hs, neg_one_smul] at h
  ext t
  have ht := congrFun h t
  simp only [Pi.neg_apply] at ht
  change columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) t = 0
  linear_combination (1 / 2 : ℂ) * ht

lemma columnAnti_basis_span (t : Tabloid μ) :
    ∃ a : ℂ, columnAnti μ (tabloidBasis μ t) = a • polytabloid μ := by
  obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective μ t
  rcases row_col_alternative μ π⁻¹ with ⟨x, y, hne, hc, hr⟩ | ⟨r, hr, c, hc, he⟩
  · exact ⟨0, by rw [columnAnti_basis_collision μ π hne hc hr, zero_smul]⟩
  · have hp : π = c⁻¹ * r⁻¹ := by simpa using congrArg Inv.inv he
    rw [hp, tabloidOfPerm_row_mul μ c⁻¹ ⟨r⁻¹, (rowStabilizer μ).inv_mem hr⟩]
    exact ⟨signC μ c⁻¹, columnAnti_basis_column μ ⟨c⁻¹, (colStabilizer μ).inv_mem hc⟩⟩

theorem columnAnti_rank_one (v : Tabloid μ → ℂ) :
    columnAnti μ v = (columnAnti μ v (tabloidOfPerm μ 1)) • polytabloid μ := by
  have hv : ∃ a : ℂ, columnAnti μ v = a • polytabloid μ := by
    choose a ha using columnAnti_basis_span μ
    refine ⟨∑ t, v t * a t, ?_⟩
    conv_lhs => rw [← sum_tabloidBasis μ v]
    rw [map_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_smul, ha, smul_smul]
  obtain ⟨a, ha⟩ := hv
  have he := congrFun ha (tabloidOfPerm μ 1)
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at he
  rw [he, ha]

lemma columnAnti_square (v : Tabloid μ → ℂ) :
    columnAnti μ (columnAnti μ v) = (Fintype.card (C μ) : ℂ) • columnAnti μ v := by
  rw [columnAnti_apply μ v]
  rw [map_sum]
  simp_rw [map_smul, columnAnti_rep, smul_smul, signC_sq, one_smul]
  rw [← columnAnti_apply]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

lemma columnAnti_polytabloid :
    columnAnti μ (polytabloid μ) = (Fintype.card (C μ) : ℂ) • polytabloid μ :=
  columnAnti_square μ _

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma antiModule_apply (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v = (tabloidRepresentation μ).asModuleEquiv.symm
      (columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v)) := rfl

lemma antiModule_rank_one (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v =
      columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) • polyModule μ := by
  rw [antiModule_apply, columnAnti_rank_one, map_smul]
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one]
  rfl

lemma polyModule_ne_zero : polyModule μ ≠ 0 := by
  intro h
  apply polytabloid_ne_zero μ
  have he := congrArg (tabloidRepresentation μ).asModuleEquiv h
  simpa only [polyModule, LinearEquiv.apply_symm_apply, map_zero] using he

lemma Specht_ne_bot : Specht μ ≠ ⊥ := by
  intro h
  have hm := polyModule_mem_Specht μ
  rw [h] at hm
  exact polyModule_ne_zero μ hm

lemma antiModule_mem (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    (v : (tabloidRepresentation μ).asModule) (hv : v ∈ U) : antiModule μ v ∈ U := by
  rw [antiModule_apply, columnAnti_apply, map_sum]
  apply U.sum_mem
  intro c hc
  have h := U.smul_mem (MonoidAlgebra.single c.val (signC μ c.val)) hv
  have he : (tabloidRepresentation μ).asModuleEquiv.symm
      (signC μ c.val • tabloidRepresentation μ c.val ((tabloidRepresentation μ).asModuleEquiv v)) =
      MonoidAlgebra.single c.val (signC μ c.val) • v := by
    apply (tabloidRepresentation μ).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
  rw [he]
  exact h

lemma scalar_polyModule_mem_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    {a : ℂ} (ha : a ≠ 0) : a • polyModule μ ∈ U ↔ polyModule μ ∈ U := by
  exact (U.restrictScalars ℂ).smul_mem_iff ha

lemma Specht_le_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule) :
    Specht μ ≤ U ↔ polyModule μ ∈ U := by
  rw [Specht, Submodule.span_le, Set.singleton_subset_iff]
  rfl

theorem Specht_isAtom : IsAtom (Specht μ) := by
  refine ⟨Specht_ne_bot μ, ?_⟩
  intro U hU
  obtain ⟨V, hUV⟩ := exists_isCompl U
  have ht : polyModule μ ∈ U ⊔ V := by
    rw [hUV.sup_eq_top]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ht
  have hau := antiModule_mem μ U u hu
  have hav := antiModule_mem μ V v hv
  rw [antiModule_rank_one] at hau hav
  by_cases hc : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv u) (tabloidOfPerm μ 1) = 0
  · have he : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) =
          (Fintype.card (C μ) : ℂ) := by
      have hh := congrArg (fun w : (tabloidRepresentation μ).asModule =>
        columnAnti μ ((tabloidRepresentation μ).asModuleEquiv w) (tabloidOfPerm μ 1)) huv
      simp only [map_add, Pi.add_apply, hc, zero_add, polyModule,
        LinearEquiv.apply_symm_apply, columnAnti_polytabloid,
        Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at hh
      exact hh
    have hne : (Fintype.card (C μ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hSV : Specht μ ≤ V := (Specht_le_iff μ V).mpr
      ((scalar_polyModule_mem_iff μ V (he.trans_ne hne)).mp hav)
    apply le_antisymm _ bot_le
    calc U ≤ U ⊓ V := le_inf le_rfl (hU.le.trans hSV)
         _ = ⊥ := hUV.inf_eq_bot
  · have hSU : Specht μ ≤ U := (Specht_le_iff μ U).mpr
      ((scalar_polyModule_mem_iff μ U hc).mp hau)
    exact (hU.not_ge hSU).elim

instance Specht_isSimpleModule : IsSimpleModule ℂ[G μ] (Specht μ) :=
  isSimpleModule_iff_isAtom.mpr (Specht_isAtom μ)

end BinaryCoordinateSweeps.Young

end

open scoped MonoidAlgebra BigOperators

namespace BinaryCoordinateSweeps.Young

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V] [IsScalarTower ℂ A V]

variable (μ : YoungDiagram)

instance instIsIrreducibleGComplexSpechtSpaceSpechtRep : Representation.IsIrreducible (k := ℂ) (G := G μ) (V := SpechtSpace μ) (spechtRep μ) :=
  (Representation.isSimpleModule_iff_irreducible_ofModule (Specht μ)).mp inferInstance

lemma spechtInclude_poly : spechtInclude μ (spechtPoly μ) = polytabloid μ := by
  change (tabloidRepresentation μ).asModuleEquiv
    ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)
      ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm
        (⟨polyModule μ, polyModule_mem_Specht μ⟩ : Specht μ))).val) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (tabloidRepresentation μ).asModuleEquiv.apply_symm_apply _

lemma spechtPoly_ne_zero : spechtPoly μ ≠ 0 := by
  intro h
  have he := congrArg (spechtInclude μ) h
  rw [map_zero, spechtInclude_poly] at he
  exact polytabloid_ne_zero μ he

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungHilbert
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

variable (μ : YoungDiagram)

instance instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht : (hilbertSpecht μ).IsIrreducible :=
  letI : AddCommGroup (SpechtSpace μ) := Module.addCommMonoidToAddCommGroup ℂ
  Irrep.irreducible_equiv _ _ (Irrep.conjugateEquiv _ _)

lemma spechtHilbertEquiv_coeff (v : SpechtSpace μ) (t : Tabloid μ) :
    (spechtHilbertEquiv μ v).val t = spechtInclude μ v t := rfl

lemma hilbertSpecht_coeff (g : G μ) (v : SpechtHilbert μ) (t : Tabloid μ) :
    (hilbertSpecht μ g v).val t = v.val (g⁻¹ • t) := by
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm
      (spechtHilbertEquiv μ w)))).val t = _
  rw [LinearEquiv.symm_apply_apply,spechtHilbertEquiv_coeff,spechtInclude_rep]
  rfl

lemma hilbertSpecht_inner (g : G μ) (v w : SpechtHilbert μ) :
    inner ℂ (hilbertSpecht μ g v) (hilbertSpecht μ g w) = inner ℂ v w := by
  change inner ℂ (hilbertSpecht μ g v).val (hilbertSpecht μ g w).val = inner ℂ v.val w.val
  simp only [PiLp.inner_apply,RCLike.inner_apply,hilbertSpecht_coeff]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun t => w.val t * star (v.val t))

lemma hilbertSpecht_unitary (g : G μ) (v : SpechtHilbert μ) :
    ‖hilbertSpecht μ g v‖ = ‖v‖ :=
  ((hilbertSpecht μ g).isometryOfInner (hilbertSpecht_inner μ g)).norm_map v

lemma hilbertSpecht_finrank : Module.finrank ℂ (SpechtHilbert μ) = Module.finrank ℂ (SpechtSpace μ) :=
  (spechtHilbertEquiv μ).finrank_eq.symm

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungInducedMap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

lemma spechtPoly_column (c : C μ) :
    spechtRep μ c.val (spechtPoly μ) = signC μ c.val • spechtPoly μ := by
  apply spechtInclude_injective μ
  simp only [spechtInclude_rep, spechtInclude_poly, map_smul]
  have he : tabloidRepresentation μ c.val (polytabloid μ) =
      signC μ c.val • polytabloid μ := by
    unfold polytabloid
    rw [columnAnti_apply, map_sum]
    have hh := Equiv.sum_comp (Equiv.mulLeft c)
      (fun d : C μ => signC μ c.val • (signC μ d.val •
        tabloidRepresentation μ d.val (tabloidBasis μ (tabloidOfPerm μ 1))))
    rw [Finset.smul_sum, ← hh]
    apply Finset.sum_congr rfl
    intro d hd
    change tabloidRepresentation μ c.val
      (signC μ d.val • tabloidRepresentation μ d.val (tabloidBasis μ (tabloidOfPerm μ 1))) =
      signC μ c.val • (signC μ (c*d).val •
        tabloidRepresentation μ (c*d).val (tabloidBasis μ (tabloidOfPerm μ 1)))
    simp only [map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
    rw [show signC μ c.val * (signC μ c.val * signC μ d.val) = signC μ d.val from by
      rw [← mul_assoc, signC_sq, one_mul]]
  exact he

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungDominance
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma filter_column_card (μ : YoungDiagram) (j k : ℕ) :
    ((columnCells μ j).filter (fun x => row x < k)).card = min k (μ.colLen j) := by
  have hinj := row_injectiveOn_column μ j
  rw [← Finset.card_image_of_injOn (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))]
  have he : (((columnCells μ j).filter (fun x => row x < k)).image row) =
      Finset.range (min k (μ.colLen j)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨x, ⟨hx, hk⟩, rfl⟩
      exact ⟨hk, Finset.mem_range.mp (image_row_columnCells μ j ▸
        Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
    · rintro ⟨hk, hj⟩
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp
        ((image_row_columnCells μ j).symm ▸ Finset.mem_range.mpr hj)
      exact ⟨x, ⟨hx, he ▸ hk⟩, he⟩
  rw [he, Finset.card_range]

lemma filter_injective_column_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j k : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ((columnCells μ j).filter (fun x => f x < k)).card ≤ min k (μ.colLen j) := by
  apply le_min
  · calc
      _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card_of_injOn f
        · intro x hx
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
        · exact hf.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
      _ = k := Finset.card_range k
  · rw [← card_columnCells μ j]
    exact Finset.card_le_card (Finset.filter_subset _ _)

lemma card_filter_eq_sum_columns (μ : YoungDiagram) (p : Cell μ → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ j ∈ (Finset.univ : Finset (Cell μ)).image col, ((columnCells μ j).filter p).card := by
  simp only [Finset.card_filter]
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) (fun x => if p x then 1 else 0)

theorem dominates_of_column_injective (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (he : ∀ j, Set.InjOn (fun x => row (e x)) (columnCells μ j)) : Dominates μ ν := by
  intro k
  have hc : rowPrefix ν k = (Finset.univ.filter (fun x : Cell μ => row (e x) < k)).card := by
    simp only [rowPrefix, Finset.card_filter]
    exact (Equiv.sum_comp e (fun x => if row x < k then 1 else 0)).symm
  rw [hc, card_filter_eq_sum_columns, rowPrefix, card_filter_eq_sum_columns]
  apply Finset.sum_le_sum
  intro j hj
  rw [filter_column_card]
  exact filter_injective_column_le μ _ j k (he j)

lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  have he : (Finset.univ.filter (fun x : Cell μ => row x < k+1)) =
      (Finset.univ.filter (fun x : Cell μ => row x < k)) ∪
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.univ.filter (fun x : Cell μ => row x < k))
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    omega
  rw [rowPrefix, he, Finset.card_union_of_disjoint hd]
  congr 1
  rw [YoungDiagram.rowLen_eq_card]
  apply Finset.card_bij (fun (x : Cell μ) _ => x.val)
  · intro x hx
    rw [YoungDiagram.mem_row_iff]
    exact ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    have h := YoungDiagram.mem_row_iff.mp hx
    exact ⟨⟨x, h.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h.2, rfl⟩

lemma dominates_antisymm {μ ν : YoungDiagram} (hμ : Dominates μ ν) (hν : Dominates ν μ) : μ = ν := by
  have hp (k : ℕ) : rowPrefix μ k = rowPrefix ν k := le_antisymm (hν k) (hμ k)
  have hr (k : ℕ) : μ.rowLen k = ν.rowLen k := by
    have h := hp (k+1)
    rw [rowPrefix_succ, rowPrefix_succ, hp k] at h
    exact Nat.add_left_cancel h
  apply SetLike.coe_injective
  ext x
  rcases x with ⟨i,j⟩
  simp only [SetLike.mem_coe, YoungDiagram.mem_iff_lt_rowLen, hr]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable {μ ν : YoungDiagram}

lemma crossAnti_apply (e : Cell μ ≃ Cell ν) (v : Tabloid ν → ℂ) :
    crossAnti e v = ∑ c : C μ, signC μ c.val •
      tabloidRepresentation ν (e.permCongr c.val) v := by
  simp [crossAnti, LinearMap.sum_apply]

lemma crossAnti_rep (e : Cell μ ≃ Cell ν) (c : C μ) (v : Tabloid ν → ℂ) :
    crossAnti e (tabloidRepresentation ν (e.permCongr c.val) v) =
      signC μ c.val • crossAnti e v := by
  rw [crossAnti_apply, crossAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val •
      (signC μ d.val • tabloidRepresentation ν (e.permCongr d.val) v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation ν (e.permCongr d.val)
    (tabloidRepresentation ν (e.permCongr c.val) v) =
    signC μ c.val • (signC μ (d*c).val •
      tabloidRepresentation ν (e.permCongr (d*c).val) v)
  simp only [Subgroup.coe_mul, map_mul, Equiv.permCongr_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

lemma crossAnti_basis_collision (e : Cell μ ≃ Cell ν) (t : Tabloid ν)
    {x y : Cell μ} (hne : x ≠ y) (hc : col x = col y) (ht : t.val (e x) = t.val (e y)) :
    crossAnti e (tabloidBasis ν t) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have he : e.permCongr c.val = Equiv.swap (e x) (e y) := by
    apply Equiv.ext
    intro z
    change e (Equiv.swap x y (e.symm z)) = _
    rw [Function.Injective.map_swap e.injective, e.apply_symm_apply]
  have hf : e.permCongr c.val • t = t := by
    rw [he]
    exact swap_fixes_tabloid ν _ ht
  have h := crossAnti_rep e c (tabloidBasis ν t)
  rw [rep_basis, hf, show signC μ c.val = -1 from signC_swap μ hne, neg_one_smul] at h
  ext u
  have hu := congrFun h u
  simp only [Pi.neg_apply] at hu
  change crossAnti e (tabloidBasis ν t) u = 0
  linear_combination (1/2 : ℂ) * hu

theorem crossAnti_eq_zero_of_not_dominates (e : Cell μ ≃ Cell ν) (h : ¬ Dominates μ ν) :
    crossAnti e = 0 := by
  have hb (t : Tabloid ν) : crossAnti e (tabloidBasis ν t) = 0 := by
    obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective ν t
    by_contra hn
    apply h
    apply dominates_of_column_injective μ ν (e.trans π.symm)
    intro j x hx y hy hxy
    by_contra hne
    apply hn
    exact crossAnti_basis_collision e _ hne
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy
  apply LinearMap.ext
  intro v
  have hv : crossAnti e v = 0 := by
    conv_lhs => rw [← sum_tabloidBasis ν v]
    simp only [map_sum, map_smul, hb, smul_zero, Finset.sum_const_zero]
  exact hv

lemma spechtInclude_column_sum :
    (∑ c : C μ, signC μ c.val • spechtRep μ c.val (spechtPoly μ)) =
      (Fintype.card (C μ) : ℂ) • spechtPoly μ := by
  apply spechtInclude_injective μ
  simp only [map_sum, map_smul, spechtInclude_rep, spechtInclude_poly]
  simpa only [columnAnti_apply] using columnAnti_polytabloid μ

theorem intertwiner_dominance (e : Cell μ ≃ Cell ν)
    (f : SpechtSpace μ →ₗ[ℂ] (Tabloid ν → ℂ))
    (hf : ∀ g v, f (spechtRep μ g v) = tabloidRepresentation ν (e.permCongr g) (f v))
    (hne : f (spechtPoly μ) ≠ 0) : Dominates μ ν := by
  by_contra h
  have he : crossAnti e (f (spechtPoly μ)) = (Fintype.card (C μ) : ℂ) • f (spechtPoly μ) := by
    rw [crossAnti_apply]
    simp_rw [← hf]
    have hh := congrArg f (spechtInclude_column_sum (μ := μ))
    simpa only [map_sum, map_smul] using hh
  rw [crossAnti_eq_zero_of_not_dominates e h, LinearMap.zero_apply] at he
  exact hne ((smul_eq_zero.mp he.symm).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem equivalence_implies_diagram_eq (e : Cell μ ≃ Cell ν)
    (f : SpechtSpace μ ≃ₗ[ℂ] SpechtSpace ν)
    (hf : ∀ g v, f (spechtRep μ g v) = spechtRep ν (e.permCongr g) (f v)) : μ = ν := by
  apply dominates_antisymm
  · apply intertwiner_dominance e ((spechtInclude ν).comp f.toLinearMap)
    · intro g v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf, spechtInclude_rep]
    · intro hz
      apply spechtPoly_ne_zero μ
      apply f.injective
      apply spechtInclude_injective ν
      simpa using hz
  · apply intertwiner_dominance e.symm ((spechtInclude μ).comp f.symm.toLinearMap)
    · intro g v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [show f.symm (spechtRep ν g v) =
        spechtRep μ (e.symm.permCongr g) (f.symm v) from by
          apply f.injective
          rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]
          congr 2
          exact (e.permCongr.apply_symm_apply g).symm]
      exact spechtInclude_rep μ _ _
    · intro hz
      apply spechtPoly_ne_zero ν
      apply f.symm.injective
      apply spechtInclude_injective μ
      simpa using hz

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

variable {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]

variable (μ : YoungDiagram)

lemma perm_same_tail_tabloid (g h : G μ)
    (he : ∀ x : Tail μ, g x.val = h x.val) : tabloidOfPerm μ g = tabloidOfPerm μ h := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  intro x
  by_cases hx : row x ≠ 0
  · have hh := he ⟨x,hx⟩
    change row (g⁻¹ (h x)) = row x
    rw [← hh]
    exact congrArg row (g.symm_apply_apply x)
  · have hx0 : row x = 0 := not_ne_iff.mp hx
    change row (g⁻¹ (h x)) = row x
    rw [hx0]
    by_contra hr
    have hh := he ⟨g⁻¹ (h x),hr⟩
    change g (g.symm (h x)) = _ at hh
    rw [g.apply_symm_apply] at hh
    have hh' : x = g⁻¹ (h x) := h.injective hh
    exact hr (hh' ▸ hx0)

lemma placementTabloid_eq (x : Tail μ ↪ Cell μ) (g : G μ)
    (hg : ∀ a : Tail μ, g a.val = x a) : placementTabloid μ x = tabloidOfPerm μ g := by
  apply perm_same_tail_tabloid
  intro a
  rw [(placement_extends μ x).choose_spec, hg]

lemma placementTabloid_surjective : Function.Surjective (placementTabloid μ) := by
  intro t
  obtain ⟨g,rfl⟩ := tabloidOfPerm_surjective μ t
  exact ⟨⟨fun a => g a.val, g.injective.comp Subtype.val_injective⟩,
    placementTabloid_eq μ _ g (fun _ => rfl)⟩

lemma spechtPlacement_injective : Function.Injective (spechtPlacement μ) := by
  intro v w h
  apply spechtInclude_injective μ
  ext t
  obtain ⟨x,rfl⟩ := placementTabloid_surjective μ t
  exact congrFun h x

theorem specht_finrank_le_placements :
    Module.finrank ℂ (SpechtSpace μ) ≤ Fintype.card (Tail μ ↪ Cell μ) := by
  simpa using LinearMap.finrank_le_finrank_of_injective (spechtPlacement_injective μ)

lemma card_tail : Fintype.card (Tail μ) = Fintype.card (Cell μ) - μ.rowLen 0 := by
  rw [Fintype.card_subtype_compl]
  congr 1
  rw [Fintype.card_subtype]
  have h := rowPrefix_succ μ 0
  simpa [rowPrefix] using h

theorem specht_finrank_le_power : Module.finrank ℂ (SpechtSpace μ) ≤
    Fintype.card (Cell μ) ^ (Fintype.card (Cell μ) - μ.rowLen 0) := by
  calc
    _ ≤ Fintype.card (Tail μ ↪ Cell μ) := specht_finrank_le_placements μ
    _ ≤ Fintype.card (Tail μ → Cell μ) := Fintype.card_le_of_injective
      (fun f : Tail μ ↪ Cell μ => (f : Tail μ → Cell μ)) DFunLike.coe_injective
    _ = _ := by rw [Fintype.card_fun, card_tail]

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ConditionalSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma groupAverage_comp_slots {X Y V : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e : X ≃ Y) (ρ : Representation ℂ (Equiv.Perm X) V) (p : Equiv.Perm Y → ℂ) :
    groupAverage (ρ.comp e.symm.permCongrHom.toMonoidHom) p =
      groupAverage ρ (fun g => p (e.permCongr g)) := by
  unfold groupAverage
  rw [← Equiv.sum_comp e.permCongr]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change ρ (e.permCongr.symm (e.permCongr g))=ρ g
  rw [Equiv.symm_apply_apply]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalRigidity
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma diagonal_rigidity_aux {X : Type*} [Fintype X] (A B : X → ℝ)
    (r c : Equiv.Perm X) (hr : ∀ x, A (r x) = A x)
    (hc : ∀ x, B (c x) = B x)
    (hd : ∀ x, A ((r*c) x) + B ((r*c) x) = A x + B x) :
    ∀ x, A (c x) = A x := by
  have hq (x : X) : B ((r*c) x) = A x + B x - A (c x) := by
    have he := hd x
    change A (r (c x)) + _ = _ at he
    rw [hr] at he
    linarith
  have hxc : ∑ x, A (c x) * B x = ∑ x, A x * B x := by
    simpa only [hc] using Equiv.sum_comp c (fun x => A x * B x)
  have hxx : ∑ x, (A (c x))^2 = ∑ x, (A x)^2 :=
    Equiv.sum_comp c (fun x => (A x)^2)
  have hprod : ∑ x, (A (c x) * A x + A (c x) * B x - (A (c x))^2) =
      ∑ x, A x * B x := by
    calc
      _ = ∑ x, A ((r*c) x) * B ((r*c) x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hq]
        change _ = A (r (c x)) * _
        rw [hr]
        ring
      _ = _ := Equiv.sum_comp (r*c) (fun x => A x * B x)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hxc] at hprod
  have hcross : ∑ x, A (c x) * A x = ∑ x, (A (c x))^2 := by linarith
  have hzero : ∑ x, (A (c x) - A x)^2 = 0 := by
    calc
      _ = (∑ x, (A (c x))^2) - 2 * (∑ x, A (c x)*A x) + ∑ x, (A x)^2 := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hcross, hxx]; ring
  intro x
  have hx : (A (c x) - A x)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (A (c x) - A x))).mp hzero x
      (Finset.mem_univ x)
  nlinarith [sq_nonneg (A (c x) - A x)]

lemma diagonal_row_column (μ : YoungDiagram) (r : rowStabilizer μ) (c : C μ)
    (hd : r.val*c.val ∈ diagonalStabilizer μ) : r = 1 ∧ c = 1 := by
  have he := diagonal_rigidity_aux (fun x : Cell μ => (row x : ℝ))
    (fun x => (col x : ℝ)) r.val c.val
    (fun x => congrArg Nat.cast (r.property x)) (fun x => congrArg Nat.cast (c.property x))
    (fun x => by exact_mod_cast hd x)
  have hc : c.val ∈ rowStabilizer μ := fun x => by exact_mod_cast he x
  have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hc,c.property⟩
  rw [row_col_intersection] at hi
  have hc1 : c = 1 := Subtype.ext hi
  have hr1 : r = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Prod.ext (r.property x)
    have hh := hd x
    rw [hc1] at hh
    change row (r.val x) + col (r.val x) = row x + col x at hh
    rw [r.property] at hh
    exact Nat.add_left_cancel hh
  exact ⟨hr1,hc1⟩

lemma diagonal_column_row (μ : YoungDiagram) (c : C μ) (r : rowStabilizer μ)
    (hd : c.val*r.val ∈ diagonalStabilizer μ) : c = 1 ∧ r = 1 := by
  have hi := (diagonalStabilizer μ).inv_mem hd
  have he : (r⁻¹).val * (c⁻¹).val ∈ diagonalStabilizer μ := by simpa using hi
  obtain ⟨hr,hc⟩ := diagonal_row_column μ r⁻¹ c⁻¹ he
  exact ⟨inv_eq_one.mp hc, inv_eq_one.mp hr⟩

variable (μ : YoungDiagram)

lemma diagonal_tabloid_eq (g h : diagonalStabilizer μ) (c : C μ) :
    tabloidOfPerm μ (g.val*c.val) = tabloidOfPerm μ h.val ↔ g = h ∧ c = 1 := by
  constructor
  · intro he
    let r : rowStabilizer μ := ⟨(g.val*c.val)⁻¹*h.val,
      (tabloidOfPerm_eq_iff μ _ _).mp he⟩
    have hr : c.val*r.val = g.val⁻¹*h.val := by dsimp only [r]; group
    have hd : c.val*r.val ∈ diagonalStabilizer μ := by
      rw [hr]
      exact (diagonalStabilizer μ).mul_mem ((diagonalStabilizer μ).inv_mem g.property) h.property
    obtain ⟨hc,hr1⟩ := diagonal_column_row μ c r hd
    refine ⟨?_,hc⟩
    rw [hc,hr1] at hr
    have hg : g.val = h.val := inv_mul_eq_one.mp (by simpa using hr.symm)
    exact Subtype.ext hg
  · rintro ⟨rfl,rfl⟩
    simp

lemma diagonal_poly_coefficient (g h : diagonalStabilizer μ) :
    tabloidRepresentation μ g.val (polytabloid μ) (tabloidOfPerm μ h.val) =
      if g = h then (1 : ℂ) else 0 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  rw [map_sum]
  simp_rw [map_smul, rep_basis, smul_tabloidOfPerm]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ h.val = tabloidOfPerm μ (g.val*c.val) ↔
      g = h ∧ c = 1 := (eq_comm).trans (diagonal_tabloid_eq μ g h c)
  simp only [he]
  by_cases hgh : g = h
  · simp [hgh]
  · simp [hgh]

theorem diagonal_polytabloids_independent : LinearIndependent ℂ
    (fun g : diagonalStabilizer μ => spechtRep μ g.val (spechtPoly μ)) := by
  apply LinearIndependent.of_comp (f := spechtInclude μ)
  rw [Fintype.linearIndependent_iff]
  intro a ha g
  have he := congrFun ha (tabloidOfPerm μ g.val)
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply] at he
  simp_rw [spechtInclude_rep, spechtInclude_poly, diagonal_poly_coefficient] at he
  simpa using he

theorem diagonal_card_le_dimension : Fintype.card (diagonalStabilizer μ) ≤
    Module.finrank ℂ (SpechtSpace μ) := by
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  exact (diagonal_polytabloids_independent μ).fintype_card_le_finrank

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalDimension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma width_add_rectangle_le_card (x : Cell μ) :
    μ.rowLen 0 + row x * (col x+1) ≤ Fintype.card (Cell μ) := by
  let f : Fin (μ.rowLen 0) ⊕ (Fin (row x) × Fin (col x+1)) → Cell μ :=
    Sum.elim (fun a => ⟨(0,a.val), YoungDiagram.mem_iff_lt_rowLen.mpr a.isLt⟩)
      (fun a => ⟨(a.1.val+1,a.2.val), μ.up_left_mem
        (show a.1.val+1 ≤ row x from a.1.isLt)
        (show a.2.val ≤ col x from Nat.le_of_lt_succ a.2.isLt) x.property⟩)
  have hf : Function.Injective f := by
    intro a b he
    have he' := congrArg Subtype.val he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hab : a = b := Fin.ext (congrArg Prod.snd he')
        exact congrArg Sum.inl hab
      | inr b =>
        have hh := congrArg Prod.fst he'
        change 0 = b.1.val+1 at hh
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hh := congrArg Prod.fst he'
        change a.1.val+1 = 0 at hh
        omega
      | inr b =>
        congr 1
        apply Prod.ext
        · apply Fin.ext
          have hh := congrArg Prod.fst he'
          change a.1.val+1 = b.1.val+1 at hh
          omega
        · exact Fin.ext (congrArg Prod.snd he')
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

lemma height_add_rectangle_le_card (x : Cell μ) :
    μ.colLen 0 + col x * (row x+1) ≤ Fintype.card (Cell μ) := by
  let y : Cell μ.transpose := ⟨x.val.swap, YoungDiagram.mem_transpose.mpr x.property⟩
  have hh := width_add_rectangle_le_card μ.transpose y
  have hc : Fintype.card (Cell μ.transpose) = Fintype.card (Cell μ) := by
    simpa only [Cell, Fintype.card_coe, YoungDiagram.card] using YoungDiagram.card_transpose μ
  simpa only [YoungDiagram.rowLen_transpose, hc, y, row, col, Prod.fst_swap, Prod.snd_swap] using hh

lemma height_width_le_card : max (μ.colLen 0) (μ.rowLen 0) ≤ Fintype.card (Cell μ) := by
  by_cases h : Nonempty (Cell μ)
  · obtain ⟨x⟩ := h
    exact max_le (by have := height_add_rectangle_le_card μ x; omega)
      (by have := width_add_rectangle_le_card μ x; omega)
  · have hempty : μ = ⊥ := by
      apply YoungDiagram.ext
      ext x
      simp only [YoungDiagram.cells_bot, Finset.notMem_empty, iff_false]
      intro hx
      exact h ⟨⟨x,hx⟩⟩
    subst μ
    simp [YoungDiagram.colLen, YoungDiagram.rowLen]

lemma diagonal_twice_le (x : Cell μ) :
    2*(diagonal μ x+1) ≤ Fintype.card (Cell μ) + max (μ.colLen 0) (μ.rowLen 0) := by
  have hr : row x < μ.colLen 0 :=
    (YoungDiagram.mem_iff_lt_colLen.mp x.property).trans_le (μ.colLen_anti 0 _ (Nat.zero_le _))
  have hc : col x < μ.rowLen 0 :=
    (YoungDiagram.mem_iff_lt_rowLen.mp x.property).trans_le (μ.rowLen_anti 0 _ (Nat.zero_le _))
  have hm := height_width_le_card μ
  unfold diagonal
  by_cases hrow : row x = 0
  · rw [hrow]
    omega
  by_cases hcol : col x = 0
  · rw [hcol]
    omega
  rcases le_total (μ.colLen 0) (μ.rowLen 0) with h | h
  · rw [max_eq_right h]
    have hh := width_add_rectangle_le_card μ x
    have hm2 : 2*row x ≤ row x*(col x+1) := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [max_eq_left h]
    have hh := height_add_rectangle_le_card μ x
    have hm2 : 2*col x ≤ col x*(row x+1) := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    omega

lemma diagonal_lt_half_card_add_max (x : Cell μ) :
    diagonal μ x < (Fintype.card (Cell μ) + max (μ.colLen 0) (μ.rowLen 0))/2 := by
  have hh := diagonal_twice_le μ x
  omega

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] [Fintype Y] in
lemma assembleFiberPerm_injective (f : X → Y) : Function.Injective (assembleFiberPerm f) := by
  intro p q he
  have hh := congrArg Subtype.val he
  have hh' : Equiv.sigmaCongrRight p = Equiv.sigmaCongrRight q :=
    (Equiv.sigmaFiberEquiv f).permCongr.injective hh
  exact Equiv.Perm.sigmaCongrRightHom_injective hh'

lemma product_factorial_le_stabilizer (f : X → Y) :
    (∏ y, (Fintype.card {x // f x = y}).factorial) ≤ Nat.card (fiberStabilizer f) := by
  have hi := Nat.card_le_card_of_injective (assembleFiberPerm f) (assembleFiberPerm_injective f)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_perm] using hi

lemma two_pow_sub_one_le_factorial (n : ℕ) : 2^(n-1) ≤ n.factorial := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_sub_one, pow_succ, Nat.factorial_succ]
      have hp : 2 ≤ n+1+1 := by omega
      simpa only [Nat.succ_sub_one, mul_comm] using Nat.mul_le_mul ih hp

lemma two_pow_card_sub_colors_le_stabilizer (f : X → Y) :
    2^(Fintype.card X - Fintype.card Y) ≤ Nat.card (fiberStabilizer f) := by
  have hsum : ∑ y, Fintype.card {x // f x = y} = Fintype.card X := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hexp : Fintype.card X - Fintype.card Y ≤
      ∑ y, (Fintype.card {x // f x = y} - 1) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (y : Y) _ =>
      show Fintype.card {x // f x = y} ≤ (Fintype.card {x // f x = y} - 1) + 1 from by omega)
    rw [hsum, Finset.sum_add_distrib] at hh
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hh
    omega
  calc
    _ ≤ 2^(∑ y, (Fintype.card {x // f x = y} - 1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = ∏ y, 2^(Fintype.card {x // f x = y} - 1) := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ y, (Fintype.card {x // f x = y}).factorial :=
      Finset.prod_le_prod' (fun y _ => two_pow_sub_one_le_factorial _)
    _ ≤ _ := product_factorial_le_stabilizer f

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceInterpolation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagPower_norm_le_one (d : ι → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd : ∀ i, d i ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖diagPower d z‖ ≤ 1 := by
  rw [diagPower, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs with hi
  · simp
  · rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hz (Real.log_nonpos (hd0 i) (hd i))

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma star_diagReal (s : ι → ℝ) : star (diagReal s) = diagReal s := by
  simp [diagReal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]

lemma diagReal_mul (s t : ι → ℝ) : diagReal s * diagReal t = diagReal (fun i => s i*t i) := by
  simp [diagReal, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

omit [DecidableEq ι] in
lemma gram_product (X Y : M ι) :
    star (X*Y) * (X*Y) = star Y * (star X * X) * Y := by
  simp only [star_mul, mul_assoc]

lemma gram_diagonal_factor (X : M ι) (s : ι → ℝ)
    (hX : star X * X = diagReal (fun i => s i ^ 2)) :
    ∃ U : M ι, ‖U‖ ≤ 1 ∧ X = U * diagReal s := by
  let t : ι → ℝ := fun i => (s i)⁻¹
  let U := X * diagReal t
  have hU : star U * U = diagReal (fun i => if s i = 0 then 0 else 1) := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    congr 1
    funext i
    dsimp [t]
    split_ifs with hi
    · simp [hi]
    · field_simp
  have hUnorm : ‖U‖ ≤ 1 := by
    have h : ‖star U * U‖ ≤ 1 := by
      rw [hU, diagReal, Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      split_ifs <;> norm_num
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg U]
  let w : ι → ℝ := fun i => 1 - t i * s i
  have hz : star (X * diagReal w) * (X * diagReal w) = 0 := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    have hw : (fun i => (w i * s i ^ 2) * w i) = 0 := by
      funext i
      dsimp [w, t]
      by_cases hi : s i = 0 <;> simp [hi]
    rw [hw]
    simp [diagReal]
  have hzero : X * diagReal w = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  have hw : diagReal w = 1 - diagReal t * diagReal s := by
    rw [diagReal_mul]
    dsimp [diagReal, w]
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp
  rw [hw, mul_sub, mul_one] at hzero
  refine ⟨U, hUnorm, ?_⟩
  exact (sub_eq_zero.mp hzero).trans (mul_assoc _ _ _).symm

theorem exists_partial_svd (A : M ι) :
    ∃ (U : M ι) (V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ ‖U‖ ≤ 1 ∧
      A = U * diagReal s * star (V : M ι) ∧
      star A * A = (V : M ι) * diagReal (fun i => s i ^ 2) * star (V : M ι) := by
  let h := Matrix.isHermitian_conjTranspose_mul_self A
  let V := h.eigenvectorUnitary
  let s : ι → ℝ := fun i => Real.sqrt (h.eigenvalues i)
  have hs0 : ∀ i, 0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hs : ∀ i, s i ^ 2 = h.eigenvalues i := fun i =>
    Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
  have hdiag : star (V : M ι) * (star A * A) * (V : M ι) =
      diagReal (fun i => s i ^ 2) := by
    simpa only [V, s, hs, diagReal, Matrix.star_eq_conjTranspose, Function.comp_def,
      Unitary.conjStarAlgAut_star_apply] using! h.conjStarAlgAut_star_eigenvectorUnitary
  have hgram : star (A * (V : M ι)) * (A * (V : M ι)) =
      diagReal (fun i => s i ^ 2) := by rw [gram_product, hdiag]
  obtain ⟨U, hU, heq⟩ := gram_diagonal_factor (A * (V : M ι)) s hgram
  have hVV : (V : M ι) * star (V : M ι) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self V
  refine ⟨U, V, s, hs0, hU, ?_, ?_⟩
  · have heq' := congrArg (fun X => X * star (V : M ι)) heq
    simpa only [mul_assoc, hVV, mul_one] using heq'
  · calc
      star A * A = ((V : M ι) * star (V : M ι)) * (star A * A) *
          ((V : M ι) * star (V : M ι)) := by rw [hVV, one_mul, mul_one]
      _ = (V : M ι) * (star (V : M ι) * (star A * A) * (V : M ι)) *
          star (V : M ι) := by simp only [mul_assoc]
      _ = _ := by rw [hdiag]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SpectralMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagReal_pow (s : ι → ℝ) (q : ℕ) :
    (diagReal s)^q = diagReal (fun i => s i ^ q) := by
  simp [diagReal, Matrix.diagonal_pow]

lemma trace_unitary_conj (V : Matrix.unitaryGroup ι ℂ) (B : M ι) :
    Matrix.trace ((V : M ι) * B * star (V : M ι)) = Matrix.trace B := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma unitary_conj_pow (V : Matrix.unitaryGroup ι ℂ) (B : M ι) (q : ℕ) :
    ((V : M ι) * B * star (V : M ι))^q = (V : M ι) * B^q * star (V : M ι) := by
  have h := ((Unitary.conjStarAlgAut ℂ (M ι) V).toAlgEquiv.map_pow B q).symm
  change (Unitary.conjStarAlgAut ℂ (M ι) V B)^q =
    Unitary.conjStarAlgAut ℂ (M ι) V (B^q) at h
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star] using h

lemma matrixMoment_of_svd (A : M ι) (q : ℕ) (V : Matrix.unitaryGroup ι ℂ)
    (s : ι → ℝ) (hgram : star A * A = (V : M ι) * diagReal (fun i => s i^2) * star (V : M ι)) :
    matrixMoment q A = ∑ i, s i ^ (2*q) := by
  rw [matrixMoment, hgram, unitary_conj_pow, trace_unitary_conj, diagReal_pow]
  simp only [diagReal, Matrix.trace_diagonal,
    Complex.re_sum, Complex.ofReal_re, ← pow_mul]

lemma matrixMoment_nonneg (q : ℕ) (A : M ι) : 0 ≤ matrixMoment q A := by
  obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  rw [matrixMoment_of_svd A q V s hg]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (hs i) _)

lemma matrixMoment_eq_zero_iff {q : ℕ} (hq : 0 < q) (A : M ι) :
    matrixMoment q A = 0 ↔ A = 0 := by
  constructor
  · intro h
    obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
    rw [matrixMoment_of_svd A q V s hg] at h
    have hi : ∀ i, s i = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => pow_nonneg (hs j) (2*q))).mp h
      exact (pow_eq_zero_iff (by omega : 2*q ≠ 0)).mp (hz i (Finset.mem_univ _))
    rw [hA]
    simp [diagReal, hi]
  · intro h
    simp [matrixMoment, h, zero_pow (by omega : q ≠ 0)]

lemma unitary_norm_le_one (V : Matrix.unitaryGroup ι ℂ) : ‖(V : M ι)‖ ≤ 1 := by
  have h1 : ‖(1 : M ι)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  have h : ‖(V : M ι)‖ * ‖(V : M ι)‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, Unitary.coe_star_mul_self]
    exact h1
  nlinarith [norm_nonneg (V : M ι)]

omit [Fintype ι] in
lemma diagPower_real (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) {x : ℝ} (hx : 0 < x) :
    diagPower d (x : ℂ) = diagReal (fun i => (d i) ^ x) := by
  unfold diagPower diagReal
  congr 1
  funext i
  by_cases hi : d i = 0
  · simp [hi, Real.zero_rpow hx.ne']
  · rw [ite_eq_right hi]
    change Complex.exp ((x : ℂ) * (Real.log (d i) : ℂ)) = ((d i ^ x : ℝ) : ℂ)
    rw [Real.rpow_def_of_pos (lt_of_le_of_ne (hd i) (Ne.symm hi))]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    ring

lemma density_normalization {m : ℕ} (hm : 0 < m) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    {t : ℝ} (ht : 0 < t) (hts : ∑ i, s i^m = t) :
    let d : ι → ℝ := fun i => s i ^ m / t
    (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
    diagReal s = (t ^ ((m : ℝ)⁻¹) : ℝ) • diagPower d (((m : ℝ)⁻¹ : ℝ) : ℂ) := by
  dsimp only
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : ∀ i, 0 ≤ s i^m/t := fun i => div_nonneg (pow_nonneg (hs i) _) ht.le
  refine ⟨hd, ?_, ?_⟩
  · rw [← Finset.sum_div, hts, div_self ht.ne']
  · rw [diagPower_real _ hd (inv_pos.mpr hm')]
    unfold diagReal
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    change (s i : ℂ) = ((t ^ (m : ℝ)⁻¹ : ℝ) : ℂ) *
      (((s i ^ m / t) ^ (m : ℝ)⁻¹ : ℝ) : ℂ)
    rw [Real.div_rpow (pow_nonneg (hs i) _) ht.le,
      Real.pow_rpow_inv_natCast (hs i) (Nat.ne_of_gt hm)]
    norm_cast
    exact (mul_div_cancel₀ (s i) (Real.rpow_pos_of_pos ht _).ne').symm

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceHolder
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalized_svd {q : ℕ} (hq : 0 < q) (A : M ι) (ht : 0 < matrixMoment q A) :
    ∃ (U V : M ι) (d : ι → ℝ), ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧
      (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
      A = (matrixMoment q A ^ ((2*q : ℕ) : ℝ)⁻¹ : ℝ) •
        (U * diagPower d ((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * V) := by
  obtain ⟨U, W, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  have hsum := matrixMoment_of_svd A q W s hg
  obtain ⟨hd, hsumd, heq⟩ := density_normalization (by omega : 0 < 2*q) s hs ht hsum.symm
  refine ⟨U, star (W : M ι), fun i => s i ^ (2*q) / matrixMoment q A,
    hU, ?_, hd, hsumd, ?_⟩
  · simpa only [norm_star] using unitary_norm_le_one W
  · conv_lhs => rw [hA, heq]
    simp only [mul_smul_comm, smul_mul_assoc]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma schatten_nonneg (q : ℕ) (A : M ι) : 0 ≤ schatten q A :=
  Real.rpow_nonneg (matrixMoment_nonneg _ _) _

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_LinearEvenMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [Fintype ι] [DecidableEq ι]

lemma trace_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (A : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V A = Matrix.trace (LinearMap.toMatrixOrthonormal v A) :=
  LinearMap.trace_eq_matrix_trace ℂ v.toBasis A

lemma evenMoment_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (q : ℕ) (A : V →ₗ[ℂ] V) :
    evenMoment q A=matrixMoment q (LinearMap.toMatrixOrthonormal v A) := by
  unfold evenMoment matrixMoment
  rw [trace_orthonormalMatrix v]
  simp only [map_pow,map_mul,← LinearMap.star_eq_adjoint,map_star]

lemma evenMoment_nonneg (q : ℕ) (A : V →ₗ[ℂ] V) : 0≤evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  exact matrixMoment_nonneg _ _

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IrrepTransport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

lemma irreducible_comp_equiv (e : H ≃* G) (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (k := ℂ) (G := H) (V := V) (ρ.comp e.toMonoidHom) :=
  (subrepresentationCongr e ρ).isSimpleOrder_iff.mp inferInstance

variable [Fintype G] [FiniteDimensional ℂ V]

lemma classPair_character_self (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    classPairRight (classCharacter ρ) (classCharacter ρ) = 1 := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  have he : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
  simpa [classPairRight, he] using Representation.char_orthonormal ρ ρ

lemma classPair_characters {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    classPairRight (classCharacter σ) (classCharacter ρ) =
      if Nonempty (Representation.Equiv σ ρ) then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  exact Representation.char_orthonormal ρ σ

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_CharacterComplete
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G I : Type*} [Group G] [Fintype G] [Fintype I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (σ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (σ i)]

theorem linearIndependent_classCharacters
    (hdiff : ∀ i j, Nonempty (Representation.Equiv (σ i) (σ j)) → i = j) :
    LinearIndependent ℂ (fun i => classCharacter (σ i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := congrArg (classPairRight (classCharacter (σ i))) ha
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
  have hi (j : I) : Nonempty (Representation.Equiv (σ i) (σ j)) ↔ i = j := by
    constructor
    · exact hdiff i j
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simp_rw [classPair_characters, hi] at h
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

theorem complete_of_card_ge [Nonempty I]
    (hdiff : ∀ i j, Nonempty (Representation.Equiv (σ i) (σ j)) → i = j)
    (hcard : Nat.card (ConjClasses G) ≤ Fintype.card I)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] :
    ∃ i, Nonempty (Representation.Equiv ρ (σ i)) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hli := linearIndependent_classCharacters σ hdiff
  have hdim : Fintype.card I = Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply le_antisymm hli.fintype_card_le_finrank
    simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using hcard
  have ht := hli.span_eq_top_of_card_eq_finrank hdim
  by_contra hn
  push Not at hn
  have hzero (i : I) : classPairRight (classCharacter ρ) (classCharacter (σ i)) = 0 := by
    have hi : ¬ Nonempty (Representation.Equiv ρ (σ i)) := fun ⟨f⟩ => (hn i).false f
    rw [classPair_characters, ite_eq_right hi]
  have hle : Submodule.span ℂ (Set.range (fun i => classCharacter (σ i))) ≤
      (classPairRight (classCharacter ρ)).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hzero i
  rw [ht] at hle
  have he : classPairRight (classCharacter ρ) (classCharacter ρ) = 0 :=
    hle (Submodule.mem_top)
  rw [classPair_character_self] at he
  exact one_ne_zero he

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungPartition
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma diagram_rowLens {n : ℕ} (p : n.Partition) :
    (diagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  apply p.parts_pos
  simpa only [Multiset.mem_sort] using hx

lemma diagram_injective {n : ℕ} : Function.Injective (diagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have hh := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [diagram_rowLens, Multiset.sort_eq] using hh

lemma conjPartition_injective {X : Type*} [Fintype X] [DecidableEq X] :
    Function.Injective (conjPartition (X := X)) := by
  intro c d
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨d, rfl⟩ := ConjClasses.mk_surjective d
  intro h
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (Equiv.Perm.partition_eq_of_isConj.mpr h)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFinite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

instance instIsIrreduciblePermFinComplexPartitionSpacePartitionRep {n : ℕ} (p : n.Partition) :
    Representation.IsIrreducible (k := ℂ) (G := Equiv.Perm (Fin n))
      (V := PartitionSpace p) (partitionRep p) :=
  Irrep.irreducible_comp_equiv _ _

lemma partitionRep_apply {n : ℕ} (p : n.Partition) (g : Equiv.Perm (Fin n))
    (v : PartitionSpace p) : partitionRep p g v =
      spechtRep (diagram p) ((cellsEquivFin p).symm.permCongr g) v := rfl

lemma partitionRep_equiv_injective {n : ℕ} (p q : n.Partition)
    (f : Representation.Equiv (partitionRep p) (partitionRep q)) : p = q := by
  apply diagram_injective
  let e := (cellsEquivFin p).trans (cellsEquivFin q).symm
  apply equivalence_implies_diagram_eq e f.toLinearEquiv
  intro g v
  have h := Representation.IntertwiningMap.isIntertwining
    (partitionRep p) (partitionRep q) f.toIntertwiningMap ((cellsEquivFin p).permCongr g) v
  simp only [partitionRep_apply] at h
  change f.toLinearEquiv _ = _ at h
  have hep : ((cellsEquivFin p).symm.permCongr ((cellsEquivFin p).permCongr g)) = g :=
    (cellsEquivFin p).permCongr.symm_apply_apply g
  rw [hep] at h
  rw [h]
  congr 2

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungClassification
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

theorem partitionRep_complete {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    ∃ p : n.Partition, Nonempty (Representation.Equiv ρ (partitionRep p)) := by
  refine Irrep.complete_of_card_ge (G := Equiv.Perm (Fin n))
    (V := fun p : n.Partition => PartitionSpace p)
    (fun p : n.Partition => partitionRep p) ?_ ?_ ρ
  · intro p q ⟨f⟩
    exact partitionRep_equiv_injective p q f
  · let : Fintype (ConjClasses (Equiv.Perm (Fin n))) := Fintype.ofFinite _
    have h := Fintype.card_le_of_injective (conjPartition (X := Fin n)) conjPartition_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h

theorem specht_complete {X V : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm X) V) [ρ.IsIrreducible] :
    ∃ (μ : YoungDiagram) (e : Cell μ ≃ X), Nonempty (Representation.Equiv ρ
      ((spechtRep μ).comp e.symm.permCongrHom.toMonoidHom)) := by
  let a : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let ρ' : Representation ℂ (Equiv.Perm (Fin (Fintype.card X))) V :=
    ρ.comp a.symm.permCongrHom.toMonoidHom
  have : ρ'.IsIrreducible := Irrep.irreducible_comp_equiv _ _
  obtain ⟨p, ⟨f⟩⟩ := partitionRep_complete ρ'
  let e : Cell (diagram p) ≃ X := (cellsEquivFin p).trans a.symm
  refine ⟨diagram p, e, ⟨Representation.Equiv.mk f.toLinearEquiv ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  have h := Representation.IntertwiningMap.isIntertwining ρ' (partitionRep p)
    f.toIntertwiningMap (a.permCongr g) v
  change f.toLinearEquiv (ρ (a.symm.permCongr (a.permCongr g)) v) =
    spechtRep (diagram p) ((cellsEquivFin p).symm.permCongr (a.permCongr g)) (f.toLinearEquiv v) at h
  rw [show a.symm.permCongr (a.permCongr g) = g from
    a.permCongr.symm_apply_apply g] at h
  exact h

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungResolution
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

instance instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep {n : ℕ} (p : n.Partition) : (partitionHilbertRep p).IsIrreducible :=
  Irrep.irreducible_comp_equiv _ _

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedLogBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma irreducible_finrank_pos {G W : Type*} [Group G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] : 0<Module.finrank ℂ W := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  rw [← ρ.asModuleEquiv.finrank_eq]
  exact Module.finrank_pos

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_WeightedCycle
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma linePerturbationRadius_lt_one (r : ℕ) : linePerturbationRadius r < 1 := by
  have hf : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  unfold linePerturbationRadius
  apply (div_lt_one (by positivity)).mpr
  linarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplit
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

lemma size_split : gridSize bits=gridSize (leftBits bits)*gridSize (rightBits bits) := by
  rw [← card_gridSlot, Fintype.card_congr (slotEquiv bits),Fintype.card_prod,
    card_gridSlot,card_gridSlot]

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenTriangle
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma norm_le_schatten {q : ℕ} (hq : 0<q) (A : M ι) : ‖A‖≤ schatten q A := by
  by_cases hz : matrixMoment q A=0
  · rw [(matrixMoment_eq_zero_iff hq A).mp hz,norm_zero]
    exact schatten_nonneg _ _
  have ht := lt_of_le_of_ne (matrixMoment_nonneg q A) (Ne.symm hz)
  obtain ⟨U,V,d,hU,hV,hd,hs,he⟩ := normalized_svd hq A ht
  have hd1 : ∀i, d i≤ 1 := by
    intro i
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  have hD : ‖diagPower d ((((2*q:ℕ):ℝ)⁻¹:ℝ):ℂ)‖≤ 1 :=
    diagPower_norm_le_one d hd hd1 (by simp)
  conv_lhs => rw [he,norm_smul,Real.norm_eq_abs]
  change |schatten q A| * _ ≤ schatten q A
  rw [abs_of_nonneg (schatten_nonneg q A)]
  apply mul_le_of_le_one_right (schatten_nonneg _ _)
  refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans hV)
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hU).trans hD)

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DenseClosing
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Young Irrep Representation GridSplit Signed

lemma diagramF_nonneg (μ : YoungDiagram) : 0≤diagramF μ := by
  apply Real.log_nonneg
  have hpos := irreducible_finrank_pos (hilbertSpecht μ)
  rw [hilbertSpecht_finrank] at hpos
  exact_mod_cast Nat.one_le_of_lt hpos

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungDimensionLower
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma two_pow_card_sub_diagonal_le_dimension (L : ℕ)
    (hL : ∀ x : Cell μ, diagonal μ x < L) :
    2^(Fintype.card (Cell μ)-L) ≤ Module.finrank ℂ (SpechtSpace μ) := by
  let f : Cell μ → Fin L := fun x => ⟨diagonal μ x,hL x⟩
  have hf : fiberStabilizer f = diagonalStabilizer μ := by
    ext g
    constructor
    · intro hg x; exact congrArg Fin.val (hg x)
    · intro hg x; exact Fin.ext (hg x)
  have hb := two_pow_card_sub_colors_le_stabilizer f
  rw [Fintype.card_fin, hf, Nat.card_eq_fintype_card] at hb
  exact hb.trans (diagonal_card_le_dimension μ)

theorem log_dimension_lower :
    (Real.log 2 / 2) *
      (Fintype.card (Cell μ) - max (μ.colLen 0) (μ.rowLen 0) : ℕ) ≤
      Real.log (Module.finrank ℂ (SpechtSpace μ)) := by
  let N := Fintype.card (Cell μ)
  let W := max (μ.colLen 0) (μ.rowLen 0)
  let L := (N+W)/2
  have hWN : W ≤ N := height_width_le_card μ
  have hLN : L ≤ N := by dsimp only [L]; omega
  have hnat : N-W ≤ 2*(N-L) := by dsimp only [L]; omega
  have hr : ((N-W : ℕ) : ℝ) ≤ 2*((N-L : ℕ) : ℝ) := by exact_mod_cast hnat
  have hb := two_pow_card_sub_diagonal_le_dimension μ L (diagonal_lt_half_card_add_max μ)
  have hbr : (2 : ℝ)^(N-L) ≤ (Module.finrank ℂ (SpechtSpace μ) : ℝ) := by exact_mod_cast hb
  have hlog := Real.log_le_log (show (0 : ℝ) < 2^(N-L) from by positivity) hbr
  rw [Real.log_pow] at hlog
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change (Real.log 2 / 2) * ((N-W : ℕ) : ℝ) ≤ _
  nlinarith

lemma tail_min_eq_card_sub_max :
    min (Fintype.card (Cell μ) - μ.rowLen 0) (Fintype.card (Cell μ) - μ.colLen 0) =
      Fintype.card (Cell μ) - max (μ.colLen 0) (μ.rowLen 0) := by omega

theorem log_dimension_lower_min_tail :
    (Real.log 2 / 2) *
      (min (Fintype.card (Cell μ)-μ.rowLen 0) (Fintype.card (Cell μ)-μ.colLen 0) : ℕ) ≤
      Real.log (Module.finrank ℂ (SpechtSpace μ)) := by
  rw [tail_min_eq_card_sub_max]
  exact log_dimension_lower μ

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTranspose
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

lemma transpose_sign (g : G μ) : signC μ.transpose ((transposeCells μ).permCongr g) =
    signC μ g := by rw [signC_eq, signC_eq, Equiv.Perm.sign_permCongr]

lemma transpose_row_to_col (r : rowStabilizer μ) :
    (transposeCells μ).permCongr r.val ∈ colStabilizer μ.transpose := by
  intro x
  exact r.property ((transposeCells μ).symm x)

lemma transpose_col_to_row (c : C μ) :
    (transposeCells μ).permCongr c.val ∈ rowStabilizer μ.transpose := by
  intro x
  exact c.property ((transposeCells μ).symm x)

instance instIsIrreducibleGComplexSpechtSpaceTransposeTransposeRep : Representation.IsIrreducible (k := ℂ) (G := G μ)
    (V := SpechtSpace μ.transpose) (transposeRep μ) :=
  Irrep.irreducible_comp_equiv _ _

lemma transposePoly_row_fixed (r : rowStabilizer μ) :
    signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) r.val (spechtPoly μ.transpose) = spechtPoly μ.transpose := by
  change signC μ r.val • spechtRep μ.transpose ((transposeCells μ).permCongr r.val)
    (spechtPoly μ.transpose) = _
  rw [spechtPoly_column μ.transpose ⟨_,transpose_row_to_col μ r⟩,
    transpose_sign, smul_smul, signC_sq, one_smul]

lemma transposeMap_intertwines (g : G μ) (v : SpechtSpace μ) :
    transposeMap μ (spechtRep μ g v) =
      signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) g (transposeMap μ v) := by
  simp only [transposeMap, LinearMap.comp_apply, spechtInclude_rep]
  exact fromTabloid_intertwines μ _ _ (transposePoly_row_fixed μ) g _

lemma row_fixes_base_evaluation (r : rowStabilizer μ) (v : Tabloid μ → ℂ) :
    tabloidRepresentation μ r.val v (tabloidOfPerm μ 1) = v (tabloidOfPerm μ 1) := by
  change v (r.val⁻¹ • tabloidOfPerm μ 1) = _
  rw [smul_tabloidOfPerm, mul_one]
  congr 1
  exact (tabloidOfPerm_eq_iff μ _ _).mpr (by simp [r.property])

lemma transposeMap_poly_evaluation : spechtInclude μ.transpose
    (transposeMap μ (spechtPoly μ)) (tabloidOfPerm μ.transpose 1) = Fintype.card (C μ) := by
  change spechtInclude μ.transpose
    (fromTabloid μ (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (spechtPoly μ.transpose)
      (spechtInclude μ (spechtPoly μ))) _ = _
  rw [spechtInclude_poly, polytabloid, columnAnti_apply, map_sum]
  simp only [map_smul, rep_basis, smul_tabloidOfPerm, mul_one, fromTabloid_basis]
  simp_rw [tabloidVector_eq μ _ _ (transposePoly_row_fixed μ)]
  have ht (c : C μ) : signC μ c.val • signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) c.val
      (spechtPoly μ.transpose) = spechtRep μ.transpose ((transposeCells μ).permCongr c.val)
        (spechtPoly μ.transpose) := by
    change signC μ c.val • (signC μ c.val •
      spechtRep μ.transpose ((transposeCells μ).permCongr c.val) (spechtPoly μ.transpose)) = _
    rw [smul_smul, signC_sq, one_smul]
  simp_rw [ht]
  rw [map_sum]
  simp only [Finset.sum_apply, spechtInclude_rep, spechtInclude_poly]
  have he (c : C μ) : tabloidRepresentation μ.transpose ((transposeCells μ).permCongr c.val)
      (polytabloid μ.transpose) (tabloidOfPerm μ.transpose 1) = 1 := by
    rw [row_fixes_base_evaluation μ.transpose ⟨_,transpose_col_to_row μ c⟩,
      polytabloid_base]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem specht_transpose_sign : Nonempty (Representation.Equiv (spechtRep μ)
    (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ))) := by
  let f := (transposeMap μ).intertwiningMap_of_isIntertwiningMap
    (spechtRep μ) (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (transposeMap_intertwines μ)
  have hn : f ≠ 0 := by
    intro h
    have hz : transposeMap μ (spechtPoly μ) = 0 := by
      exact congrArg (fun g : Representation.IntertwiningMap (spechtRep μ)
        (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) => g (spechtPoly μ)) h
    have he := transposeMap_poly_evaluation μ
    rw [hz, map_zero, Pi.zero_apply] at he
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card (C μ) : ℂ) ≠ 0) he.symm
  have : (signTwist μ (transposeRep μ)).IsIrreducible :=
    signTwist_irreducible μ (transposeRep μ)
  have hf := (Representation.IsIrreducible.bijective_or_eq_zero (k := ℂ) (G := G μ)
    (V := SpechtSpace μ) (W := SpechtSpace μ.transpose) f).resolve_right hn
  exact ⟨f.ofBijective hf⟩

lemma specht_finrank_transpose : Module.finrank ℂ (SpechtSpace μ) =
    Module.finrank ℂ (SpechtSpace μ.transpose) := by
  obtain ⟨e⟩ := specht_transpose_sign μ
  exact e.toLinearEquiv.finrank_eq

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseReduction
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.Young
open Irrep Signed

lemma diagramF_le_rowTail (μ : YoungDiagram) (s : ℕ) (hs : 0 < s)
    (hM : Fintype.card (Cell μ) ≤ s) :
    diagramF μ  ≤  (Fintype.card (Cell μ)-μ.rowLen 0:ℕ)*Real.log s := by
  have hD : (0:ℝ) < Module.finrank ℂ (SpechtSpace μ) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht μ)
  have hb := (specht_finrank_le_power μ).trans (Nat.pow_le_pow_left hM _)
  have hl := (Real.log_le_log_iff hD (pow_pos (Nat.cast_pos.mpr hs) _)).mpr
    (show (Module.finrank ℂ (SpechtSpace μ):ℝ) ≤
    (s:ℝ)^(Fintype.card (Cell μ)-μ.rowLen 0) by exact_mod_cast hb)
  rw [Real.log_pow] at hl
  exact hl

lemma diagramF_transpose (μ : YoungDiagram) : diagramF μ.transpose=diagramF μ := by
  unfold diagramF
  rw [←specht_finrank_transpose]

lemma minTail_orientation (μ : YoungDiagram) :
    Fintype.card (Tail μ)=minTail μ ∨ Fintype.card (Tail μ.transpose)=minTail μ := by
  have hc := Fintype.card_congr (transposeCells μ)
  rw [card_tail,card_tail,YoungDiagram.rowLen_transpose,←hc]
  exact (le_total (Fintype.card (Cell μ)-μ.rowLen 0) (Fintype.card (Cell μ)-μ.colLen 0)).elim
    (fun h => Or.inl (min_eq_left h).symm) (fun h => Or.inr (min_eq_right h).symm)

lemma diagramF_le_minTail (μ : YoungDiagram) (s : ℕ) (hs : 0 < s)
    (hM : Fintype.card (Cell μ) ≤ s) : diagramF μ ≤ (minTail μ:ℝ)*Real.log s := by
  rcases minTail_orientation μ with ht | ht
  · simpa only [←card_tail,ht] using diagramF_le_rowTail μ s hs hM
  · have hc : Fintype.card (Cell μ.transpose) ≤ s :=
      (Fintype.card_congr (transposeCells μ)).symm.trans_le hM
    simpa only [diagramF_transpose,←card_tail,ht] using diagramF_le_rowTail μ.transpose s hs hc

lemma minTail_le_diagramF (μ : YoungDiagram) :
    (minTail μ:ℝ) ≤ (2/Real.log 2)*diagramF μ := by
  have hl := log_dimension_lower_min_tail μ
  have htwo := Real.log_pos (by norm_num : (1:ℝ) < 2)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ htwo).mpr
  change Real.log 2/2*(minTail μ:ℝ) ≤ diagramF μ at hl
  nlinarith

end BinaryCoordinateSweeps.Young
namespace BinaryCoordinateSweeps
open Young Irrep Signed

lemma const_mul_rpow_eventually (C u v : ℝ) (huv : u < v) : ∀ᶠ s : ℕ in atTop,
    C*(s:ℝ)^u ≤ (s:ℝ)^v := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr huv)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop C,eventually_ge_atTop (1:ℕ)] with s hs hs1
  have hp : (0:ℝ) < s := by exact_mod_cast hs1
  calc
    _  ≤  (s:ℝ)^(v-u)*(s:ℝ)^u := mul_le_mul_of_nonneg_right hs (Real.rpow_pos_of_pos hp _).le
    _ = _ := by rw [←Real.rpow_add hp]; congr 1; ring

lemma sparse_reduction_eventually : ∀ᶠ s : ℕ in atTop,
    ∀ b r h : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1 ≤ b →
    (∀j,r ≤ bits j) → 400000000 ≤ (r:ℝ)*Real.log 2 →
    ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀_e : Cell μ ≃ FreeSlot H 0,
    diagramF μ < (s:ℝ)^(399/400:ℝ) →
    ¬((1+cExponent s)*diagramF μ ≤ eExponent s*h*Real.log s-pathCost H) →
    1 ≤ minTail μ ∧ h ≤ 100000*minTail μ ∧
      ((minTail μ+h:ℕ):ℝ) ≤ (s:ℝ)^(1599/1600:ℝ) := by
  filter_upwards [const_mul_rpow_eventually (80000+2/Real.log 2) (399/400) (1599/1600)
    (by norm_num)] with s hs
  intro b r h bits he hb hd hr H μ e hF hnot
  have ha := grid_parameter_allowance hb hd hr H
  rw [he] at ha
  have hLF := grid_log_lower hd
  rw [he] at hLF
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hL : 1 ≤ Real.log s := by nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg b)]
  have hF0 := diagramF_nonneg μ
  have hM : Fintype.card (Cell μ) ≤ s := by
    rw [Fintype.card_congr e,card_freeSlot,he]
    exact Nat.sub_le _ _
  have hp : 0 < s := he ▸ gridSize_pos bits
  have hupper := diagramF_le_minTail μ s hp hM
  have hlow := minTail_le_diagramF μ
  have hallow0 : 0 ≤ eExponent s*h*Real.log s-pathCost H := by
    apply le_trans _ ha.2.2
    unfold e0
    positivity
  have hc : cExponent s ≤ 1 := by have := ha.1; unfold c0 at this; linarith
  have hn := lt_of_not_ge hnot
  have hhL : (h:ℝ)*Real.log s < 80000*diagramF μ := by
    have hh := ha.2.2
    unfold e0 at hh
    nlinarith [mul_le_mul_of_nonneg_right hc hF0]
  have hkpos : 0 < minTail μ := by
    by_contra hk
    have hk0 : minTail μ=0 := by omega
    rw [hk0,Nat.cast_zero,zero_mul] at hupper
    have : diagramF μ=0 := le_antisymm hupper hF0
    rw [this,mul_zero] at hn
    linarith
  have hhk : h ≤ 100000*minTail μ := by
    have hr' : (h:ℝ) ≤ 100000*(minTail μ:ℝ) := by
      have hh' := hhL.trans_le (mul_le_mul_of_nonneg_left hupper (by norm_num))
      have : (h:ℝ) < 80000*minTail μ := by nlinarith
      nlinarith [show (0:ℝ) ≤ minTail μ by positivity]
    exact_mod_cast hr'
  refine ⟨hkpos,hhk,?_⟩
  have hhF : (h:ℝ) ≤ 80000*diagramF μ := by nlinarith
  have hsum : ((minTail μ+h:ℕ):ℝ) ≤ (80000+2/Real.log 2)*diagramF μ := by
    push_cast
    nlinarith
  refine hsum.trans ((mul_le_mul_of_nonneg_left hF.le ?_).trans hs)
  have := Real.log_pos (by norm_num : (1:ℝ) < 2)
  positivity

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_FewSparseBases
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

lemma grid_log_upper {b r : ℕ} {bits : Fin b → ℕ} (hd : ∀j, bits j ≤ 2*r) :
    Real.log (gridSize bits) ≤ (b:ℝ)*(2*(r:ℝ)*Real.log 2) := by
  calc
    _ = ∑j : Fin b, (bits j:ℝ)*Real.log 2 := by
      rw [log_gridSize]
      simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    _  ≤  ∑_j : Fin b, 2*(r:ℝ)*Real.log 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd j) (Real.log_nonneg (by norm_num))
    _ = _ := by simp

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_BalancedGrid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open GridSplit

lemma balanced_counts (b : ℕ) (hb : 2 ≤ b) : ∃m n : ℕ,
    b=m+n ∧ 1 ≤ m ∧ 1 ≤ n ∧ m < b ∧ n < b ∧ m ≤ 2*n ∧ n ≤ 2*m := by
  refine ⟨b/2,b-b/2,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

lemma balanced_grid_bounds {m n r : ℕ} (bits : Fin (m+n) → ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≤ 2*n) (hnm : n ≤ 2*m)
    (hd : ∀j,r ≤ bits j ∧ bits j ≤ 2*r) (hr : 400000000 ≤ (r:ℝ)*Real.log 2) :
    1 ≤ Real.log (gridSize (leftBits bits)) ∧ 1 ≤ Real.log (gridSize (rightBits bits)) ∧
    Real.log (gridSize (leftBits bits)) ≤ (4/5:ℝ)*Real.log (gridSize bits) ∧
    Real.log (gridSize (rightBits bits)) ≤ (4/5:ℝ)*Real.log (gridSize bits) ∧
    Real.log 4*(m+n) ≤ (1/1000:ℝ)*Real.log (gridSize bits) := by
  have hl := grid_log_lower (fun j : Fin m => (hd (j.castAdd n)).1)
  have hr' := grid_log_lower (fun j : Fin n => (hd (j.natAdd m)).1)
  have hlu := grid_log_upper (fun j : Fin m => (hd (j.castAdd n)).2)
  have hru := grid_log_upper (fun j : Fin n => (hd (j.natAdd m)).2)
  change (m:ℝ)*((r:ℝ)*Real.log 2) ≤ Real.log (gridSize (leftBits bits)) at hl
  change (n:ℝ)*((r:ℝ)*Real.log 2) ≤ Real.log (gridSize (rightBits bits)) at hr'
  change Real.log (gridSize (leftBits bits)) ≤ (m:ℝ)*(2*r*Real.log 2) at hlu
  change Real.log (gridSize (rightBits bits)) ≤ (n:ℝ)*(2*r*Real.log 2) at hru
  have hsum : Real.log (gridSize bits)=Real.log (gridSize (leftBits bits))+Real.log (gridSize (rightBits bits)) := by
    rw [size_split,Nat.cast_mul]
    exact Real.log_mul (by exact_mod_cast (gridSize_pos (leftBits bits)).ne')
      (by exact_mod_cast (gridSize_pos (rightBits bits)).ne')
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmnR : (m:ℝ) ≤ 2*n := by exact_mod_cast hmn
  have hnmR : (n:ℝ) ≤ 2*m := by exact_mod_cast hnm
  have hscale : 0 ≤ (r:ℝ)*Real.log 2 := by linarith
  have hmnl := mul_le_mul_of_nonneg_right hmnR hscale
  have hnml := mul_le_mul_of_nonneg_right hnmR hscale
  have hm1 := mul_le_mul_of_nonneg_right hmR hscale
  have hn1 := mul_le_mul_of_nonneg_right hnR hscale
  have haxes := grid_log_lower (fun j => (hd j).1)
  have hlog4 : Real.log 4 ≤ 4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hbR : (0:ℝ) ≤ m+n := by positivity
  have hax := mul_le_mul_of_nonneg_right hlog4 hbR
  have hsc := mul_le_mul_of_nonneg_left hr hbR
  push_cast at haxes
  refine ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_HilbertMainCases
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Signed

lemma logMoment_le_iff_le_exp (T x : ℝ) : logMoment T ≤ (x:EReal) ↔ T ≤ Real.exp x := by
  by_cases hT : T ≤ 0
  · simp only [logMoment,ENNReal.ofReal_eq_zero.mpr hT, ENNReal.log_zero,bot_le,true_iff]
    exact hT.trans (Real.exp_pos _).le
  · have hT' := lt_of_not_ge hT
    rw [logMoment,ENNReal.log_ofReal_of_pos hT',EReal.coe_le_coe_iff]
    exact Real.log_le_iff_le_exp hT'

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma hilbert_conditional_dimension {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (q : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) :
    evenMoment q (groupAverage ρ (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Module.finrank ℂ V := by
  let E := (stdOrthonormalBasis ℂ V).repr
  let σ := conjugateRep ρ E.toLinearEquiv
  have hσ (g) (v) : ‖σ g v‖=‖v‖ := by
    change ‖E (ρ g (E.symm v))‖=‖v‖
    rw [E.norm_map,hρ,E.symm.norm_map]
  have he := equivalent_evenMoment ρ σ (conjugateEquiv ρ E.toLinearEquiv) hρ hσ
    (fun g => (conditionalGroupLaw H z g:ℂ)) q
  rw [he,←conditionalMoment_evenMoment H z σ q]
  exact traceMoment_le_dimension q _ (conditionalOperator_norm_le_one H hz hz1 σ hσ)

lemma hilbert_conditional_automatic {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (q : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (ha : (1+cExponent (gridSize bits))*Real.log (Module.finrank ℂ V) ≤
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H) :
    evenMoment q (groupAverage ρ (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
    Real.exp (-cExponent (gridSize bits)*Real.log (Module.finrank ℂ V)+
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H) := by
  have hD : (0:ℝ) < Module.finrank ℂ V := by exact_mod_cast irreducible_finrank_pos ρ
  refine (hilbert_conditional_dimension H z hz hz1 q ρ hρ).trans ?_
  rw [←Real.exp_log hD]
  apply Real.exp_le_exp.mpr
  rw [Real.log_exp]
  linarith

lemma hilbert_conditional_one_axis {r q : ℕ}
    (hr : (400000000:ℝ) ≤ (r:ℝ)*Real.log 2) (hq : 0 < q)
    (bits : Fin 1 → ℕ) (hd : ∀j,r ≤ bits j ∧ bits j ≤ 2*r)
    {h : ℕ} (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hzr : z ≤ oneAxisRadius r)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) [ρ.IsIrreducible]
    (hρ : ∀g v,‖ρ g v‖=‖v‖) :
    evenMoment q (groupAverage ρ (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
    Real.exp (-cExponent (gridSize bits)*Real.log (Module.finrank ℂ V)+
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H) := by
  let E := (stdOrthonormalBasis ℂ V).repr
  let σ := conjugateRep ρ E.toLinearEquiv
  have : σ.IsIrreducible := irreducible_equiv ρ σ (conjugateEquiv ρ E.toLinearEquiv)
  have hσ (g) (v) : ‖σ g v‖=‖v‖ := by
    change ‖E (ρ g (E.symm v))‖=‖v‖
    rw [E.norm_map,hρ,E.symm.norm_map]
  have he := equivalent_evenMoment ρ σ (conjugateEquiv ρ E.toLinearEquiv) hρ hσ
    (fun g => (conditionalGroupLaw H z g:ℂ)) q
  rw [he,←conditionalMoment_evenMoment H z σ q]
  exact (logMoment_le_iff_le_exp _ _).mp (conditional_moment_one_axis hr hq bits hd H hz hzr σ hσ)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_HilbertTranspose
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Representation

variable (μ : YoungDiagram)

lemma norm_signC (g : G μ) : ‖signC μ g‖=1 := by
  have h := congrArg Norm.norm (signC_sq μ g)
  rw [norm_mul,norm_one] at h
  nlinarith [norm_nonneg (signC μ g)]

lemma hilbert_transpose_equiv : Nonempty ((hilbertSpecht μ).Equiv
    (signTwist μ ((hilbertSpecht μ.transpose).comp (transposeCells μ).permCongrHom.toMonoidHom))) := by
  obtain ⟨f⟩ := specht_transpose_sign μ
  let E := (spechtHilbertEquiv μ).symm.trans (f.toLinearEquiv.trans (spechtHilbertEquiv μ.transpose))
  refine ⟨.mk E ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change spechtHilbertEquiv μ.transpose
      (f.toLinearEquiv.toFun ((spechtHilbertEquiv μ).symm.toFun
        (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm.toFun
          (spechtHilbertEquiv μ w)))))) =
    signC μ g • spechtHilbertEquiv μ.transpose
      (spechtRep μ.transpose ((transposeCells μ).permCongr g)
        ((spechtHilbertEquiv μ.transpose).symm.toFun
          (spechtHilbertEquiv μ.transpose (f.toLinearEquiv.toFun
            ((spechtHilbertEquiv μ).symm.toFun (spechtHilbertEquiv μ w))))))
  have hs (ν : YoungDiagram) (x : SpechtSpace ν) :
      (spechtHilbertEquiv ν).symm.toFun (spechtHilbertEquiv ν x) = x :=
    (spechtHilbertEquiv ν).symm_apply_apply x
  simp only [hs]
  have h := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g w
  change f.toLinearEquiv.toFun (spechtRep μ g w) = signC μ g •
    spechtRep μ.transpose ((transposeCells μ).permCongr g) (f.toLinearEquiv.toFun w) at h
  exact (congrArg (spechtHilbertEquiv μ.transpose).toFun h).trans (map_smul _ _ _)

lemma hilbert_transpose_moment (p : G μ → ℂ) (q : ℕ) :
    evenMoment q (groupAverage (hilbertSpecht μ) p) =
      evenMoment q (groupAverage (hilbertSpecht μ.transpose)
        (fun g => p ((transposeCells μ).symm.permCongr g)*signC μ.transpose g)) := by
  obtain ⟨f⟩ := hilbert_transpose_equiv μ
  rw [equivalent_evenMoment _ _ f (hilbertSpecht_unitary μ) (fun g v => by
    change ‖signC μ g • hilbertSpecht μ.transpose ((transposeCells μ).permCongr g) v‖=‖v‖
    rw [norm_smul,norm_signC,hilbertSpecht_unitary,one_mul])]
  congr 1
  unfold groupAverage
  rw [←Equiv.sum_comp (transposeCells μ).permCongr]
  apply Finset.sum_congr rfl
  intro g _
  change p g • (signC μ g • hilbertSpecht μ.transpose ((transposeCells μ).permCongr g)) = _
  dsimp only
  rw [smul_smul,transpose_sign]
  rw [show (transposeCells μ).symm.permCongr ((transposeCells μ).permCongr g)=g from
    (transposeCells μ).permCongr.symm_apply_apply g]

end BinaryCoordinateSweeps.Young
namespace BinaryCoordinateSweeps
open Young Irrep

lemma realSign_permCongr_complex {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X≃Y) (g : Equiv.Perm X) :
    (realSign (e.permCongr g):ℂ)=(realSign g:ℂ) := by
  exact congrArg (fun sign : ℤˣ => (((sign : ℤ) : ℝ) : ℂ))
    (Equiv.Perm.sign_permCongr e g)

lemma conditional_transpose_moment {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0) (z : ℝ) (q : ℕ) :
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) =
    evenMoment q (groupAverage ((hilbertSpecht μ.transpose).comp
      ((transposeCells μ).symm.trans e).symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) := by
  rw [groupAverage_comp_slots,groupAverage_comp_slots,hilbert_transpose_moment]
  congr 2
  funext g
  congr 1
  rw [realSign_permCongr_complex]
  change ((Equiv.Perm.sign g:ℤ):ℂ)=(((Equiv.Perm.sign g:ℤ):ℝ):ℂ)
  norm_cast

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_ManySparse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Young Irrep

theorem sparse_closing_radius : ∃ S : ℕ, ∀r : ℕ, 2 ≤ r →
    4000000000 ≤ (r:ℝ)*Real.log 2 →
    ∃δ : ℝ, 0 < δ ∧ δ ≤ linePerturbationRadius r ∧ ∀s : ℕ, S ≤ s →
    ∀b h : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1 ≤ b →
    (∀j,r ≤ bits j ∧ bits j ≤ 2*r) → (10:ℝ)^26 ≤ Real.log s →
    ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
    diagramF μ < (s:ℝ)^(399/400:ℝ) → ∀z : ℝ, 0 ≤ z → z ≤ δ →
    evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
      Real.exp (-cExponent s*diagramF μ+eExponent s*h*Real.log s-pathCost H) := by
  obtain ⟨S,hS⟩ := sparse_uniform_radius
  obtain ⟨T,hT⟩ := eventually_atTop.mp sparse_reduction_eventually
  refine ⟨max S T,?_⟩
  intro r hr hrL
  obtain ⟨δ,hδ,hδline,hsp⟩ := hS r hr hrL
  refine ⟨δ,hδ,hδline,?_⟩
  intro s hSs
  have hs := hsp s ((le_max_left S T).trans hSs)
  have hred := hT s ((le_max_right S T).trans hSs)
  intro b h bits he hb hd hL H μ e hF z hz hzδ
  have := irreducible_comp_equiv e.symm.permCongrHom (hilbertSpecht μ)
  have hz1 := (hzδ.trans hδline).trans_lt (linePerturbationRadius_lt_one r)
  have hunit (g : Equiv.Perm (FreeSlot H 0)) (v : SpechtHilbert μ) :
      ‖((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) g v‖=‖v‖ :=
    hilbertSpecht_unitary μ _ v
  by_cases ha : (1+cExponent s)*diagramF μ ≤ eExponent s*h*Real.log s-pathCost H
  · have hh := hilbert_conditional_automatic H z hz hz1 mainMomentPower _ hunit
    simp only [hilbertSpecht_finrank,he] at hh
    exact hh ha
  · obtain ⟨hk,hh,htail⟩ := hred b r h bits he hb (fun j => (hd j).1) (by linarith) H μ e hF ha
    let k := minTail μ
    have hm : Fintype.card (Cell μ) ≤ s := by
      rw [Fintype.card_congr e,card_freeSlot,he]
      exact Nat.sub_le _ _
    have hupper := diagramF_le_minTail μ s (he ▸ gridSize_pos bits) hm
    have hg := grid_parameter_allowance hb (fun j => (hd j).1) (by linarith : 400000000 ≤ (r:ℝ)*Real.log 2) H
    rw [he] at hg
    have hc : cExponent s ≤ 1 := by have := hg.1; unfold c0 at this; linarith
    have hallow : 0 ≤ eExponent s*h*Real.log s-pathCost H := by
      apply le_trans _ hg.2.2
      unfold e0
      positivity
    have hbound : evenMoment mainMomentPower
        (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
          (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s) := by
      rcases minTail_orientation μ with ht | ht
      · let a : Tail μ ≃ Fin k := (Fintype.equivFin _).trans (finCongr ht)
        exact (hs b h k bits he hb hd hL hk htail hh H μ e a z hz hzδ).1
      · let a : Tail μ.transpose ≃ Fin k := (Fintype.equivFin _).trans (finCongr ht)
        rw [conditional_transpose_moment]
        exact (hs b h k bits he hb hd hL hk htail hh H μ.transpose ((transposeCells μ).symm.trans e)
          a z hz hzδ).2
    refine hbound.trans (Real.exp_le_exp.mpr ?_)
    have hF0 := diagramF_nonneg μ
    change diagramF μ ≤ (k:ℝ)*Real.log s at hupper
    nlinarith [mul_le_mul_of_nonneg_right hc hF0]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_MainMomentInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Irrep Representation Signed

lemma spechtMomentBound_enumerated {q b : ℕ} {bits : Fin b → ℕ} {z : ℝ}
    (hB : SpechtMomentBound q bits z) : EnumeratedMomentBound q bits z := by
  intro h H α
  let e : Cell (diagram α) ≃ FreeSlot H 0 :=
    (cellsEquivFin α).trans (Fintype.equivFin _).symm
  have hb := hB h H (diagram α) e
  have he : groupAverage ((hilbertSpecht (diagram α)).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ)) =
      groupAverage (partitionHilbertRep α)
        (fun a => (conditionalGroupLaw H z ((Fintype.equivFin _).symm.permCongr a):ℂ)) := by
    rw [groupAverage_comp_slots]
    symm
    rw [partitionHilbertRep,groupAverage_comp_slots]
    rfl
  rw [he] at hb
  simpa only [typeF,hilbertSpecht_finrank,diagramF] using hb

lemma hilbert_specht_complete {X V : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm X) V) [ρ.IsIrreducible] :
    ∃(μ : YoungDiagram) (e : Cell μ ≃ X), Nonempty (ρ.Equiv
      ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)) := by
  obtain ⟨μ,e,⟨f⟩⟩ := specht_complete ρ
  let σ : Representation ℂ (Equiv.Perm X) (SpechtSpace μ) := (spechtRep μ).comp e.symm.permCongrHom.toMonoidHom
  let τ : Representation ℂ (Equiv.Perm X) (SpechtHilbert μ) := (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom
  have a : σ.Equiv τ := .mk (spechtHilbertEquiv μ) (by
    intro g
    apply LinearMap.ext
    intro v
    change spechtHilbertEquiv μ (spechtRep μ _ v)=
      spechtHilbertEquiv μ (spechtRep μ _ ((spechtHilbertEquiv μ).symm (spechtHilbertEquiv μ v)))
    rw [LinearEquiv.symm_apply_apply])
  exact ⟨μ,e,⟨f.trans a⟩⟩

lemma spechtMomentBound_main {q b : ℕ} {bits : Fin b → ℕ} {z : ℝ}
    (hB : SpechtMomentBound q bits z) (h D : ℕ) (H : PathFamily bits h)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) :
    logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
      ((-cExponent (gridSize bits)*Real.log D+
        eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H:ℝ):EReal) := by
  obtain ⟨μ,e,⟨f⟩⟩ := hilbert_specht_complete ρ
  have he := equivalent_evenMoment _ _ f hρ (fun g v => hilbertSpecht_unitary μ _ v)
    (fun g => (conditionalGroupLaw H z g:ℂ)) q
  have hD := f.toLinearEquiv.finrank_eq
  rw [finrank_euclideanSpace_fin,hilbertSpecht_finrank] at hD
  apply (logMoment_le_iff_le_exp _ _).mpr
  rw [conditionalMoment_evenMoment,he]
  simpa only [hD,diagramF] using hB h H μ e

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Young Irrep Representation GridSplit

theorem conditional_moment_main : ConditionalMomentTarget := by
  obtain ⟨S,hS⟩ := sparse_closing_radius
  have hq : 2 ≤ mainMomentPower := by norm_num [mainMomentPower]
  obtain ⟨T,hT⟩ := eventually_atTop.mp (dense_induction_step_eventually mainMomentPower hq)
  let A : ℝ := max ((10:ℝ)^26) ((max S T:ℕ):ℝ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨r,hr⟩ := exists_nat_gt (max (2:ℝ) (A/Real.log 2))
  have hr2 : 2 ≤ r := by
    have : (2:ℝ) < r := (le_max_left _ _).trans_lt hr
    exact_mod_cast this.le
  have hrA : A ≤ (r:ℝ)*Real.log 2 := by
    have : A/Real.log 2 < r := (le_max_right _ _).trans_lt hr
    exact (div_lt_iff₀ hlog2).mp this |>.le
  have hrL : (10:ℝ)^26 ≤ (r:ℝ)*Real.log 2 := (le_max_left _ _).trans hrA
  have hrM : ((max S T:ℕ):ℝ) ≤ (r:ℝ)*Real.log 2 := (le_max_right _ _).trans hrA
  have hr4 : (4000000000:ℝ) ≤ (r:ℝ)*Real.log 2 := by linarith
  obtain ⟨δ,hδ,hδline,hsp⟩ := hS r hr2 hr4
  let zStar := min δ (oneAxisRadius r)
  have hzStar : 0 < zStar := lt_min hδ (oneAxisRadius_pos r)
  have hlarge {b : ℕ} (hb : 1 ≤ b) (bits : Fin b → ℕ)
      (hd : ∀j,r ≤ bits j ∧ bits j ≤ 2*r) :
      max S T ≤ gridSize bits ∧ (10:ℝ)^26 ≤ Real.log (gridSize bits) := by
    have hl := grid_log_lower (fun j => (hd j).1)
    have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
    have hr0 : 0 ≤ (r:ℝ)*Real.log 2 := by positivity
    have hbase : (r:ℝ)*Real.log 2 ≤ Real.log (gridSize bits) := by
      have := mul_le_mul_of_nonneg_right hbR hr0
      nlinarith
    refine ⟨?_,hrL.trans hbase⟩
    have hpos : (0:ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
    have hexp := Real.log_le_sub_one_of_pos hpos
    have : ((max S T:ℕ):ℝ) ≤ gridSize bits := by linarith [hrM.trans hbase]
    exact_mod_cast this
  have hproof : ∀b : ℕ, 1 ≤ b → ∀bits : Fin b → ℕ,
      (∀j,r ≤ bits j ∧ bits j ≤ 2*r) → ∀z : ℝ, 0 ≤ z → z ≤ zStar →
      SpechtMomentBound mainMomentPower bits z := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hb bits hd z hz hzr h H μ e
      by_cases hb1 : b=1
      · subst b
        have := irreducible_comp_equiv e.symm.permCongrHom (hilbertSpecht μ)
        have hbase := hilbert_conditional_one_axis (by linarith : (400000000:ℝ) ≤ (r:ℝ)*Real.log 2)
          (by omega : 0 < mainMomentPower) bits hd H hz (hzr.trans (min_le_right _ _))
          ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
          (fun g v => hilbertSpecht_unitary μ _ v)
        simpa only [hilbertSpecht_finrank,diagramF] using hbase
      · have hb2 : 2 ≤ b := by omega
        obtain ⟨m,n,rfl,hm,hn,hmb,hnb,hmn,hnm⟩ := balanced_counts b hb2
        obtain ⟨hsize,hL⟩ := hlarge hb bits hd
        by_cases hF : (gridSize bits:ℝ)^(399/400:ℝ) ≤ diagramF μ
        · obtain ⟨hu,hv,hub,hvb,haxes⟩ := balanced_grid_bounds bits hm hn hmn hnm hd (by linarith)
          apply hT (gridSize bits) ((le_max_right S T).trans hsize) m n h r bits H rfl
            hu hv hub hvb (fun j => (hd j).2) haxes μ e hF z hz
            ((hzr.trans (min_le_left _ _)).trans hδline)
          · apply spechtMomentBound_enumerated
            exact ih m hmb hm (leftBits bits) (fun j => hd (j.castAdd n)) z hz hzr
          · apply spechtMomentBound_enumerated
            exact ih n hnb hn (rightBits bits) (fun j => hd (j.natAdd m)) z hz hzr
        · exact hsp (gridSize bits) ((le_max_left S T).trans hsize) (m+n) h bits rfl hb hd hL H μ e
            (lt_of_not_ge hF) z hz (hzr.trans (min_le_left _ _))
  refine ⟨r,by omega,mainMomentPower,by omega,zStar,hzStar,?_⟩
  intro b hb bits hd h H z hz hzr D ρ hi hρ
  have := hi
  exact spechtMomentBound_main (hproof b hb bits hd z hz hzr) h D H ρ hρ

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_MomentOperatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Classical

namespace BinaryCoordinateSweeps
open TraceHolder Irrep

lemma norm_le_momentRoot {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (hq : 0<q) (A : M ι) :
    ‖A‖ ≤ matrixMoment q A ^ (((2*q:ℕ):ℝ)⁻¹) := by
  exact norm_le_schatten hq A

lemma norm_le_traceMomentRoot {D q : ℕ} (hq : 0<q)
    (K : RepSpace D →L[ℂ] RepSpace D) :
    ‖K‖≤traceMoment q K ^ (((2*q:ℕ):ℝ)⁻¹) := by
  let v := EuclideanSpace.basisFun (Fin D) ℂ
  let A := LinearMap.toMatrixOrthonormal v K.toLinearMap
  have he : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin D)) A=K := by
    apply ContinuousLinearMap.coe_injective
    change (LinearMap.toMatrixOrthonormal v).symm
      (LinearMap.toMatrixOrthonormal v K.toLinearMap) = K.toLinearMap
    exact StarAlgEquiv.symm_apply_apply _ _
  have hm : traceMoment q K=matrixMoment q A := by
    have hh := evenMoment_orthonormalMatrix v q K.toLinearMap
    simpa only [traceMoment,evenMoment,ContinuousLinearMap.toLinearMap_pow,
      ContinuousLinearMap.toLinearMap_mul,ContinuousLinearMap.adjoint_toLinearMap] using hh
  rw [hm,←he,Matrix.l2_opNorm_toEuclideanCLM]
  exact norm_le_momentRoot hq A

lemma opNorm_of_logMoment {D q : ℕ} (hq : 0<q) (K : RepSpace D →L[ℂ] RepSpace D)
    {a : ℝ} (h : logMoment (traceMoment q K)≤(a:EReal)) :
    ‖K‖≤Real.exp (a/(2*q)) := by
  have ht := (logMoment_le_iff_le_exp _ _).mp h
  have hm := (norm_le_traceMomentRoot hq K).trans
    (Real.rpow_le_rpow (by
      have hh := evenMoment_nonneg q K.toLinearMap
      simpa only [traceMoment,evenMoment,ContinuousLinearMap.toLinearMap_pow,
        ContinuousLinearMap.toLinearMap_mul,ContinuousLinearMap.adjoint_toLinearMap] using hh) ht (by positivity))
  rw [← Real.exp_mul] at hm
  simpa only [Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv] using hm

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_EmptyGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

lemma emptyPaths_event (g : GridChoices bits) : pathEvent (emptyPaths bits) g := by
  intro j k; exact k.elim0

lemma emptyPerm (g : GridChoices bits) (hg : pathEvent (emptyPaths bits) g) :
    (emptyFree bits 0).permCongr (remainingPerm (emptyPaths bits) g hg)=
      emptyFrame bits * gridSweep bits g := by
  ext x
  rfl

lemma empty_normalizer (z : ℝ) : conditionalNormalizer (emptyPaths bits) z=1 := by
  simp only [conditionalNormalizer,emptyPaths_event,ite_true,gridWeight_sum]

lemma empty_cost : pathCost (emptyPaths bits)=0 := by
  have hh (j : Fin b) (y : GridOutside bits j) : lineHoles (emptyPaths bits) j y=0 := by
    unfold lineHoles
    exact Fintype.card_eq_zero
  simp [pathCost,hh]

lemma empty_operator {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D))
    (z : ℝ) (x : RepSpace D) :
    conditionalOperator (emptyPaths bits) z
      (ρ.comp (emptyFree bits 0).permCongrHom.toMonoidHom) x=
    ρ (emptyFrame bits) (complexGridAverage bits ρ (z:ℂ) x) := by
  rw [conditionalOperator_apply,empty_normalizer]
  simp only [Complex.ofReal_one,inv_one,one_smul,dite_true,emptyPaths_event]
  simp only [complexGridAverage,sum_apply,smul_apply,
    complexGridWeight_real,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change ρ ((emptyFree bits 0).permCongr (remainingPerm _ g _)) x= _
  rw [emptyPerm,map_mul]
  rfl

lemma empty_operator_norm {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D))
    (hρ : IsUnitaryRep ρ) (z : ℝ) :
    ‖conditionalOperator (emptyPaths bits) z
      (ρ.comp (emptyFree bits 0).permCongrHom.toMonoidHom)‖=
    ‖complexGridAverage bits ρ (z:ℂ)‖ := by
  apply ContinuousLinearMap.opNorm_ext
  intro x
  rw [empty_operator,hρ]

theorem real_grid_bound_oai : ∃ r : ℕ, 0 < r ∧ ∃ q : ℕ, 0 < q ∧
    ∃ a : ℝ, 0 < a ∧ ∀b : ℕ, 1 ≤ b → ∀bits : Fin b → ℕ,
    (∀j, r ≤ bits j ∧ bits j ≤ 2*r) → ∀D : ℕ,
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D),
    ρ.IsIrreducible → IsUnitaryRep ρ → ∀z : ℝ, 0 ≤ z → z ≤ a →
    ‖complexGridAverage bits ρ (z:ℂ)‖ ≤ (D:ℝ)^(-c0/(2*q)) := by
  obtain ⟨r,hr,q,hq,a,ha,h⟩ := conditional_moment_main
  refine ⟨r,hr,q,hq,a,ha,?_⟩
  intro b hb bits hd D ρ hi hρ z hz hza
  let := hi
  let σ : Representation ℂ (Equiv.Perm (FreeSlot (emptyPaths bits) 0)) (RepSpace D) := ρ.comp (emptyFree bits 0).permCongrHom.toMonoidHom
  have hiσ : σ.IsIrreducible := Irrep.irreducible_comp_equiv _ ρ
  have huσ : IsUnitaryRep σ := fun g x => hρ _ x
  have hlog := h b hb bits hd 0 (emptyPaths bits) z hz hza D σ hiσ huσ
  simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero,empty_cost,sub_zero] at hlog
  have hop := opNorm_of_logMoment hq _ hlog
  rw [empty_operator_norm bits ρ hρ z] at hop
  have hD : 0 < D := by
    simpa only [RepSpace,finrank_euclideanSpace,Fintype.card_fin] using
      Signed.irreducible_finrank_pos ρ
  have hD' : 0 < (D:ℝ) := by exact_mod_cast hD
  have hc : c0  ≤  cExponent (gridSize bits) := by
    unfold cExponent
    exact le_add_of_nonneg_right (by positivity)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hqe : 0 < (2:ℝ)*q := by positivity
  have hh : (-cExponent (gridSize bits)*Real.log D)/(2*q) ≤
      (-c0/(2*q))*Real.log D := by
    apply (div_le_iff₀ hqe).mpr
    have := mul_le_mul_of_nonneg_right hc hlogD
    field_simp
    nlinarith
  apply hop.trans
  rw [Real.rpow_def_of_pos hD']
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hh

end BinaryCoordinateSweeps

end

end OAI
end

theorem solution : type_of% @OAI.BinaryCoordinateSweeps.real_grid_bound_oai := @OAI.BinaryCoordinateSweeps.real_grid_bound_oai
