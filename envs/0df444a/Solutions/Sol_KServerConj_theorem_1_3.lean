-- Prove2me | solution 1 for KServerConj.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:55:28.222919+00:00
-- url     : https://prove2.me/submissions/6c0502cb-7b94-4a2c-9792-ee1b4b460058

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_confDist
import Definitions.Def_KServerConj_workFn
import Definitions.Def_KServerConj_IsWFATraj
import Definitions.Def_KServerConj_opt
import Definitions.Def_KServerConj_cl
import Definitions.Def_KServerConj_symProd
import Definitions.Def_KServerConj_minorVal
import Definitions.Def_KServerConj_Psi
import Definitions.Def_KServerConj_K
import Definitions.Def_KServerConj_Hmat
import Definitions.Def_KServerConj_rowReplace
import Definitions.Def_KServerConj_initCols
import Definitions.Def_KServerConj_IsRun
import Definitions.Def_KServerConj_extCost
import Definitions.Def_KServerConj_colDet
set_option autoImplicit false

section PaperFile001
open scoped BigOperators

namespace KServerConj

theorem confDist_equiv_nonempty {M : Type*} (X Y : Finset M) (hXY : X.card = Y.card) :
    Nonempty (X ≃ Y) := by
  exact ⟨Fintype.equivOfCardEq (by simpa using hXY)⟩

theorem confDist_costs_bdd {M : Type*} [PseudoMetricSpace M] (X Y : Finset M) :
    BddBelow (Set.range fun e : X ≃ Y => ∑ x : X, dist (x : M) (e x : M)) := by
  exact ⟨0, fun _ ⟨e, he⟩ => he ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩

theorem confDist_le_matching {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (e : X ≃ Y) :
    confDist X Y ≤ ∑ x : X, dist (x : M) (e x : M) := by
  exact ciInf_le (confDist_costs_bdd X Y) e

theorem confDist_minimizer {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (hXY : X.card = Y.card) :
    ∃ e : X ≃ Y, (∑ x : X, dist (x : M) (e x : M)) = confDist X Y := by
  let : Nonempty (X ≃ Y) := confDist_equiv_nonempty X Y hXY
  exact exists_eq_ciInf_of_finite

theorem confDist_nonneg {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (hXY : X.card = Y.card) : 0 ≤ confDist X Y := by
  obtain ⟨e, he⟩ := confDist_minimizer X Y hXY
  exact he ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)

theorem confDist_self {M : Type*} [PseudoMetricSpace M] (X : Finset M) :
    confDist X X = 0 := by
  exact le_antisymm (by simpa using confDist_le_matching X X (Equiv.refl X))
    (confDist_nonneg X X rfl)

theorem matching_cost_inverse {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (e : X ≃ Y) :
    (∑ x : X, dist (x : M) (e x : M)) = ∑ y : Y, dist (y : M) (e.symm y : M) := by
  simpa only [Equiv.symm_apply_apply, dist_comm] using
    e.sum_comp (fun y : Y => dist (y : M) (e.symm y : M))

theorem confDist_symm {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (hXY : X.card = Y.card) : confDist X Y = confDist Y X := by
  obtain ⟨e, he⟩ := confDist_minimizer X Y hXY
  obtain ⟨f, hf⟩ := confDist_minimizer Y X hXY.symm
  exact le_antisymm
    ((confDist_le_matching X Y f.symm).trans_eq ((matching_cost_inverse Y X f).symm.trans hf))
    ((confDist_le_matching Y X e.symm).trans_eq ((matching_cost_inverse X Y e).symm.trans he))

theorem confDist_nonneg_all {M : Type*} [PseudoMetricSpace M] (X Y : Finset M) :
    0 ≤ confDist X Y := by
  classical
  by_cases hXY : X.card = Y.card
  · exact confDist_nonneg X Y hXY
  · let : IsEmpty (X ≃ Y) := ⟨fun e => hXY (by simpa using Fintype.card_congr e)⟩
    simp [confDist]

theorem confDist_triangle {M : Type*} [PseudoMetricSpace M]
    (X Y Z : Finset M) (hXY : X.card = Y.card) (hYZ : Y.card = Z.card) :
    confDist X Z ≤ confDist X Y + confDist Y Z := by
  obtain ⟨e, he⟩ := confDist_minimizer X Y hXY
  obtain ⟨f, hf⟩ := confDist_minimizer Y Z hYZ
  calc
    confDist X Z ≤ ∑ x : X, dist (x : M) (f (e x) : M) :=
      confDist_le_matching X Z (e.trans f)
    _ ≤ ∑ x : X, (dist (x : M) (e x : M) + dist (e x : M) (f (e x) : M)) :=
      Finset.sum_le_sum (fun _ _ => dist_triangle _ _ _)
    _ = (∑ x : X, dist (x : M) (e x : M)) + ∑ y : Y, dist (y : M) (f y : M) := by
      rw [Finset.sum_add_distrib, e.sum_comp (fun y : Y => dist (y : M) (f y : M))]
    _ = confDist X Y + confDist Y Z := by rw [he, hf]

end KServerConj
end PaperFile001

section PaperFile002
open scoped BigOperators

namespace KServerConj

theorem equivMap_val {N M : Type*} (f : N ↪ M) (X : Finset N) (x : X) :
    (Finset.equivMap f X x : M) = f (x : N) := rfl

noncomputable def mapMatching {N M : Type*} (f : N ↪ M) (X Y : Finset N)
    (e : X ≃ Y) : (X.map f : Finset M) ≃ (Y.map f : Finset M) :=
  (((Finset.equivMap f X).symm.trans e).trans (Finset.equivMap f Y))

theorem mapMatching_cost {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) (hd : ∀ x y, dist (f x) (f y) = dist x y)
    (X Y : Finset N) (e : X ≃ Y) :
    (∑ x : (X.map f : Finset M), dist (x : M) (mapMatching f X Y e x : M)) =
      ∑ x : X, dist (x : N) (e x : N) := by
  simpa only [mapMatching, Equiv.trans_apply, Equiv.symm_apply_apply, equivMap_val, hd] using
    ((Finset.equivMap f X).sum_comp
      (fun x : (X.map f : Finset M) => dist (x : M) (mapMatching f X Y e x : M))).symm

theorem confDist_map_embedding {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) (hd : ∀ x y, dist (f x) (f y) = dist x y)
    (X Y : Finset N) (hXY : X.card = Y.card) :
    confDist (X.map f) (Y.map f) = confDist X Y := by
  obtain ⟨e, he⟩ := confDist_minimizer X Y hXY
  have hupper : confDist (X.map f) (Y.map f) ≤ confDist X Y :=
    (confDist_le_matching _ _ (mapMatching f X Y e)).trans_eq ((mapMatching_cost f hd X Y e).trans he)
  obtain ⟨em, hem⟩ := confDist_minimizer (X.map f) (Y.map f)
    (by simpa only [Finset.card_map] using hXY)
  let eb : X ≃ Y := ((Finset.equivMap f X).trans em).trans (Finset.equivMap f Y).symm
  have hround : mapMatching f X Y eb = em := by
    apply Equiv.ext
    intro x
    simp only [mapMatching, eb, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hc := mapMatching_cost f hd X Y eb
  rw [hround] at hc
  exact le_antisymm hupper ((confDist_le_matching X Y eb).trans_eq (hc.symm.trans hem))

end KServerConj
end PaperFile002

section PaperFile003
open scoped BigOperators

namespace KServerConj

noncomputable def updateConfigEquiv {M : Type*} [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hr : r ∉ X) :
    X ≃ {z : M // z ∈ insert r (X.erase x)} := by
  refine (Equiv.swap x r).subtypeEquiv ?_
  intro z
  have hxr : x ≠ r := fun h => hr (h ▸ hx)
  by_cases hzx : z = x <;> by_cases hzr : z = r <;>
    simp_all [Equiv.swap_apply_def]

theorem card_insert_erase_admissible {M : Type*} [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hvalid : r ∉ X ∨ x = r) :
    (insert r (X.erase x)).card = X.card := by
  rcases hvalid with hr | rfl
  · simpa using (Fintype.card_congr (updateConfigEquiv X x hx r hr)).symm
  · rw [Finset.insert_erase hx]

theorem updateConfigEquiv_apply {M : Type*} [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hr : r ∉ X) (y : X) :
    (updateConfigEquiv X x hx r hr y : M) = Equiv.swap x r (y : M) := rfl

theorem updateConfigEquiv_cost {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hr : r ∉ X) :
    (∑ y : X, dist (y : M) (updateConfigEquiv X x hx r hr y : M)) = dist x r := by
  classical
  simp only [updateConfigEquiv_apply]
  rw [Finset.sum_eq_single (⟨x, hx⟩ : X)]
  · simp
  · intro y _hy hy
    have hyx : (y : M) ≠ x := fun h => hy (Subtype.ext h)
    have hyr : (y : M) ≠ r := fun h => hr (h ▸ y.property)
    simp [Equiv.swap_apply_def, hyx, hyr]
  · simp

theorem confDist_insert_erase_le {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hvalid : r ∉ X ∨ x = r) :
    confDist (insert r (X.erase x)) X ≤ dist r x := by
  rcases hvalid with hr | rfl
  · rw [confDist_symm _ X (card_insert_erase_admissible X x hx r (Or.inl hr))]
    exact (confDist_le_matching X _ (updateConfigEquiv X x hx r hr)).trans_eq
      ((updateConfigEquiv_cost X x hx r hr).trans (dist_comm x r))
  · simpa only [Finset.insert_erase hx, confDist_self, dist_self] using (le_refl (0 : ℝ))

end KServerConj
end PaperFile003

section PaperFile005
open scoped BigOperators

namespace KServerConj

theorem isSchedule_zero {M : Type*} (k : ℕ) (C₀ : Finset M) (r : ℕ → M)
    (S : ℕ → Finset M) : IsSchedule k C₀ r 0 S ↔ S 0 = C₀ := by
  exact ⟨And.left, fun h => ⟨h, fun _ hs hst =>
    False.elim (Nat.not_succ_le_zero 0 (hs.trans hst))⟩⟩

theorem IsSchedule.card {M : Type*} {k t : ℕ} {C₀ : Finset M} {r : ℕ → M}
    {S : ℕ → Finset M} (hS : IsSchedule k C₀ r t S) (hC₀ : C₀.card = k)
    (s : ℕ) (hst : s ≤ t) : (S s).card = k := by
  by_cases hs : s = 0
  · simpa only [hs, hS.1] using hC₀
  · exact (hS.2 s (Nat.one_le_iff_ne_zero.mpr hs) hst).1

theorem IsSchedule.mono {M : Type*} {k t u : ℕ} {C₀ : Finset M} {r : ℕ → M}
    {S : ℕ → Finset M} (hS : IsSchedule k C₀ r t S) (hut : u ≤ t) :
    IsSchedule k C₀ r u S := by
  exact ⟨hS.1, fun s hs hsu => hS.2 s hs (hsu.trans hut)⟩

theorem workFn_zero {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (X : Finset M) :
    workFn k C₀ r 0 X = confDist C₀ X := by
  unfold workFn
  simp only [isSchedule_zero, Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1),
    Finset.sum_empty, zero_add]
  have hset : {c : ℝ | ∃ S : ℕ → Finset M, S 0 = C₀ ∧ c = confDist (S 0) X} =
      {confDist C₀ X} := by
    ext c
    constructor
    · rintro ⟨S, hS, hc⟩
      simpa only [Set.mem_singleton_iff, hS] using hc
    · intro hc
      exact ⟨fun _ => C₀, rfl, hc⟩
  rw [hset, csInf_singleton]

theorem schedule_cost_nonneg {M : Type*} [PseudoMetricSpace M]
    (S : ℕ → Finset M) (t : ℕ) (X : Finset M) :
    0 ≤ (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => confDist_nonneg_all _ _))
    (confDist_nonneg_all _ _)

theorem workFn_costs_bdd {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M) :
    BddBelow {c : ℝ | ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S ∧
      c = (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X} := by
  exact ⟨0, fun _ ⟨S, _, hc⟩ => hc.symm ▸ schedule_cost_nonneg S t X⟩

theorem workFn_le_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M)
    (S : ℕ → Finset M) (hS : IsSchedule k C₀ r t S) :
    workFn k C₀ r t X ≤
      (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  exact csInf_le (workFn_costs_bdd k C₀ r t X) ⟨S, hS, rfl⟩

theorem workFn_costs_nonempty {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M)
    (hex : ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S) :
    {c : ℝ | ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S ∧
      c = (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X}.Nonempty := by
  exact hex.elim (fun S hS => ⟨_, S, hS, rfl⟩)

theorem workFn_nonneg_of_exists_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M)
    (hex : ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S) : 0 ≤ workFn k C₀ r t X := by
  exact le_csInf (workFn_costs_nonempty k C₀ r t X hex)
    (fun _ ⟨S, _, hc⟩ => hc.symm ▸ schedule_cost_nonneg S t X)

theorem workFn_lipschitz_of_exists_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ)
    (hex : ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S)
    (X Y : Finset M) (hX : X.card = k) (hY : Y.card = k) :
    workFn k C₀ r t Y ≤ workFn k C₀ r t X + confDist X Y := by
  apply (sub_le_iff_le_add).mp
  apply le_csInf (workFn_costs_nonempty k C₀ r t X hex)
  rintro c ⟨S, hS, rfl⟩
  have htri := confDist_triangle (S t) X Y
    ((hS.card hC₀ t le_rfl).trans hX.symm) (hX.trans hY.symm)
  have hb := workFn_le_schedule k C₀ r t Y S hS
  linarith

end KServerConj
end PaperFile005

section PaperFile006
namespace KServerConj

theorem exists_serving_config {M : Type*} [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : M) :
    ∃ Y : Finset M, Y.card = k ∧ r ∈ Y := by
  by_cases hr : r ∈ C₀
  · exact ⟨C₀, hC₀, hr⟩
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp (hC₀.symm ▸ hk)
    exact ⟨insert r (C₀.erase x),
      (card_insert_erase_admissible C₀ x hx r (Or.inl hr)).trans hC₀,
      Finset.mem_insert_self _ _⟩

theorem exists_schedule {M : Type*}
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ) :
    ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S := by
  classical
  refine ⟨fun s => if s = 0 then C₀ else (exists_serving_config k hk C₀ hC₀ (r s)).choose,
    by simp, ?_⟩
  intro s hs _hst
  simpa only [if_neg (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hs))] using
    (exists_serving_config k hk C₀ hC₀ (r s)).choose_spec

theorem workFn_nonneg {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k)
    (r : ℕ → M) (t : ℕ) (X : Finset M) : 0 ≤ workFn k C₀ r t X := by
  exact workFn_nonneg_of_exists_schedule k C₀ r t X (exists_schedule k hk C₀ hC₀ r t)

theorem workFn_lipschitz {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ)
    (X Y : Finset M) (hX : X.card = k) (hY : Y.card = k) :
    workFn k C₀ r t Y ≤ workFn k C₀ r t X + confDist X Y := by
  exact workFn_lipschitz_of_exists_schedule k C₀ hC₀ r t
    (exists_schedule k hk C₀ hC₀ r t) X Y hX hY

end KServerConj
end PaperFile006

section PaperFile007
open scoped BigOperators

namespace KServerConj

theorem IsSchedule.append_terminal {M : Type*} {k t : ℕ} {C₀ : Finset M} {r : ℕ → M}
    {S : ℕ → Finset M} (hS : IsSchedule k C₀ r t S)
    (X : Finset M) (hX : X.card = k) (hr : r (t + 1) ∈ X) :
    IsSchedule k C₀ r (t + 1) (Function.update S (t + 1) X) := by
  refine ⟨?_, ?_⟩
  · simpa only [Function.update_of_ne (by omega : 0 ≠ t + 1)] using hS.1
  · intro s hs hst
    by_cases he : s = t + 1
    · simpa only [he, Function.update_self] using And.intro hX hr
    · simpa only [Function.update_of_ne he] using hS.2 s hs (by omega)

theorem schedule_prefix_update_last {M : Type*} [PseudoMetricSpace M]
    (S : ℕ → Finset M) (t : ℕ) (X : Finset M) :
    (∑ s ∈ Finset.Icc 1 t,
      confDist (Function.update S (t + 1) X (s - 1)) (Function.update S (t + 1) X s)) =
      ∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s) := by
  apply Finset.sum_congr rfl
  intro s hs
  have hst : s ≤ t := (Finset.mem_Icc.mp hs).2
  simp only [Function.update_of_ne (by omega : s - 1 ≠ t + 1),
    Function.update_of_ne (by omega : s ≠ t + 1)]

theorem schedule_cost_update_last {M : Type*} [PseudoMetricSpace M]
    (S : ℕ → Finset M) (t : ℕ) (X : Finset M) :
    (∑ s ∈ Finset.Icc 1 (t + 1),
      confDist (Function.update S (t + 1) X (s - 1)) (Function.update S (t + 1) X s)) +
        confDist (Function.update S (t + 1) X (t + 1)) X =
      (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), schedule_prefix_update_last]
  simp only [Nat.add_sub_cancel, Function.update_self,
    Function.update_of_ne (by omega : t ≠ t + 1), confDist_self, add_zero]

end KServerConj
end PaperFile007

section PaperFile008
open scoped BigOperators

namespace KServerConj

theorem workFn_mono_succ {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (X : Finset M) (hX : X.card = k) :
    workFn k C₀ r t X ≤ workFn k C₀ r (t + 1) X := by
  apply le_csInf (workFn_costs_nonempty k C₀ r (t + 1) X
    (exists_schedule k hk C₀ hC₀ r (t + 1)))
  rintro c ⟨S, hS, rfl⟩
  have h₀ := hS.card hC₀ t (Nat.le_succ t)
  have h₁ := hS.card hC₀ (t + 1) le_rfl
  have hb := workFn_le_schedule k C₀ r t X S (hS.mono (Nat.le_succ t))
  have htri := confDist_triangle (S t) (S (t + 1)) X
    (h₀.trans h₁.symm) (h₁.trans hX.symm)
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1)]
  simp only [Nat.add_sub_cancel]
  linarith

theorem workFn_covered_succ {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (X : Finset M) (hX : X.card = k) (hr : r (t + 1) ∈ X) :
    workFn k C₀ r (t + 1) X = workFn k C₀ r t X := by
  apply le_antisymm ?_ (workFn_mono_succ k hk C₀ hC₀ r t X hX)
  apply le_csInf (workFn_costs_nonempty k C₀ r t X (exists_schedule k hk C₀ hC₀ r t))
  rintro c ⟨S, hS, rfl⟩
  have hb := workFn_le_schedule k C₀ r (t + 1) X (Function.update S (t + 1) X)
    (hS.append_terminal X hX hr)
  simpa only [schedule_cost_update_last] using hb

theorem workFn_mono {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k) :
    workFn k C₀ r (t - 1) X ≤ workFn k C₀ r t X := by
  simpa only [Nat.sub_add_cancel ht] using workFn_mono_succ k hk C₀ hC₀ r (t - 1) X hX

theorem workFn_covered {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k) (hr : r t ∈ X) :
    workFn k C₀ r t X = workFn k C₀ r (t - 1) X := by
  simpa only [Nat.sub_add_cancel ht] using workFn_covered_succ k hk C₀ hC₀ r (t - 1) X hX
    (by simpa only [Nat.sub_add_cancel ht] using hr)

theorem workFn_rec_le {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k)
    (x : M) (hx : x ∈ X) (hvalid : r t ∉ X ∨ x = r t) :
    workFn k C₀ r t X ≤
      workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x := by
  have hY := (card_insert_erase_admissible X x hx (r t) hvalid).trans hX
  have hcover := workFn_covered k hk C₀ hC₀ r t ht (insert (r t) (X.erase x)) hY
    (Finset.mem_insert_self _ _)
  have hle := workFn_lipschitz k hk C₀ hC₀ r t (insert (r t) (X.erase x)) X hY hX
  rw [hcover] at hle
  exact hle.trans (add_le_add le_rfl (confDist_insert_erase_le X x hx (r t) hvalid))

end KServerConj
end PaperFile008

section PaperFile009
open scoped BigOperators

namespace KServerConj

theorem matching_replacement_cost {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X Y : Finset M) (r : M) (hrY : r ∈ Y) (hrX : r ∉ X) (e : Y ≃ X) :
    let ry : Y := ⟨r, hrY⟩
    let x : M := (e ry : M)
    let f := updateConfigEquiv X x (e ry).property r hrX
    (∑ y : Y, dist (y : M) (f (e y) : M)) + dist r x =
      ∑ y : Y, dist (y : M) (e y : M) := by
  let ry : Y := ⟨r, hrY⟩
  let x : M := (e ry : M)
  let f := updateConfigEquiv X x (e ry).property r hrX
  have hcost (y : Y) :
      dist (y : M) (f (e y) : M) + (if y = ry then dist r x else 0) =
        dist (y : M) (e y : M) := by
    by_cases hy : y = ry
    · simp [hy, ry, x, f, updateConfigEquiv_apply]
    · have hyx : (e y : M) ≠ x := fun h => hy (e.injective (Subtype.ext h))
      have hyr : (e y : M) ≠ r := fun h => hrX (h ▸ (e y).property)
      simp [hy, f, updateConfigEquiv_apply, Equiv.swap_apply_def, hyx, hyr]
  simpa only [Finset.sum_add_distrib, Fintype.sum_ite_eq'] using
    (show (∑ y : Y, (dist (y : M) (f (e y) : M) + if y = ry then dist r x else 0)) =
      ∑ y : Y, dist (y : M) (e y : M) from
        Finset.sum_congr rfl (fun y _ => hcost y))

theorem confDist_exchange_missing {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X Y : Finset M) (hYX : Y.card = X.card) (r : M) (hrY : r ∈ Y) (hrX : r ∉ X) :
    ∃ x ∈ X, confDist Y (insert r (X.erase x)) + dist r x ≤ confDist Y X := by
  obtain ⟨e, he⟩ := confDist_minimizer Y X hYX
  let ry : Y := ⟨r, hrY⟩
  let x : M := (e ry : M)
  let f := updateConfigEquiv X x (e ry).property r hrX
  exact ⟨x, (e ry).property,
    (add_le_add (confDist_le_matching Y _ (e.trans f)) (le_refl (dist r x))).trans_eq
      ((matching_replacement_cost X Y r hrY hrX e).trans he)⟩

theorem confDist_served_exchange {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X Y : Finset M) (hYX : Y.card = X.card) (r : M) (hrY : r ∈ Y) :
    ∃ x ∈ X, (r ∉ X ∨ x = r) ∧
      confDist Y (insert r (X.erase x)) + dist r x ≤ confDist Y X := by
  by_cases hrX : r ∈ X
  · exact ⟨r, hrX, Or.inr rfl, by
      simpa only [Finset.insert_erase hrX, dist_self, add_zero] using
        (le_refl (confDist Y X))⟩
  · exact (confDist_exchange_missing X Y hYX r hrY hrX).elim
      (fun x ⟨hx, hcost⟩ => ⟨x, hx, Or.inl hrX, hcost⟩)

end KServerConj
end PaperFile009

section PaperFile010
open scoped BigOperators

namespace KServerConj

theorem schedule_to_replacement_cost {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (k : ℕ) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k)
    (S : ℕ → Finset M) (hS : IsSchedule k C₀ r t S) :
    ∃ x ∈ X, (r t ∉ X ∨ x = r t) ∧
      workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x ≤
        (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  have hlast := hS.2 t ht le_rfl
  obtain ⟨x, hx, hvalid, hexch⟩ := confDist_served_exchange X (S t)
    (hlast.1.trans hX.symm) (r t) hlast.2
  have hY := (card_insert_erase_admissible X x hx (r t) hvalid).trans hX
  have hprev := hS.card hC₀ (t - 1) (Nat.sub_le t 1)
  have hb := workFn_le_schedule k C₀ r (t - 1) (insert (r t) (X.erase x)) S
    (hS.mono (Nat.sub_le t 1))
  have htri := confDist_triangle (S (t - 1)) (S t) (insert (r t) (X.erase x))
    (hprev.trans hlast.1.symm) (hlast.1.trans hY.symm)
  have hsum : (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) =
      (∑ s ∈ Finset.Icc 1 (t - 1), confDist (S (s - 1)) (S s)) +
        confDist (S (t - 1)) (S t) := by
    simpa only [Nat.sub_add_cancel ht] using
      Finset.sum_Icc_succ_top (by omega : 1 ≤ (t - 1) + 1)
        (fun s => confDist (S (s - 1)) (S s))
  exact ⟨x, hx, hvalid, by rw [hsum]; linarith⟩

theorem admissible_point_nonempty {M : Type*} [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (X : Finset M) (hX : X.card = k) (r : M) :
    Nonempty {x : X // r ∉ X ∨ (x : M) = r} := by
  by_cases hr : r ∈ X
  · exact ⟨⟨⟨r, hr⟩, Or.inr rfl⟩⟩
  · exact (Finset.card_pos.mp (hX.symm ▸ hk)).elim
      (fun x hx => ⟨⟨⟨x, hx⟩, Or.inl hr⟩⟩)

theorem workFn_rec_ge {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k) :
    ∃ x ∈ X, (r t ∉ X ∨ x = r t) ∧
      workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x ≤
        workFn k C₀ r t X := by
  let A := {x : X // r t ∉ X ∨ (x : M) = r t}
  let f (a : A) : ℝ :=
    workFn k C₀ r (t - 1) (insert (r t) (X.erase (a.1 : M))) + dist (r t) (a.1 : M)
  let : Nonempty A := admissible_point_nonempty k hk X hX (r t)
  have hfb : BddBelow (Set.range f) :=
    ⟨0, fun _ ⟨a, ha⟩ => ha ▸ add_nonneg
      (workFn_nonneg k hk C₀ hC₀ r (t - 1) (insert (r t) (X.erase (a.1 : M)))) dist_nonneg⟩
  have hmin : (⨅ a : A, f a) ≤ workFn k C₀ r t X := by
    apply le_csInf (workFn_costs_nonempty k C₀ r t X (exists_schedule k hk C₀ hC₀ r t))
    rintro c ⟨S, hS, rfl⟩
    obtain ⟨x, hx, hvalid, hcost⟩ := schedule_to_replacement_cost k C₀ hC₀ r t ht X hX S hS
    exact (ciInf_le hfb (⟨⟨x, hx⟩, hvalid⟩ : A)).trans hcost
  obtain ⟨a, ha⟩ : ∃ a : A, f a = ⨅ a : A, f a := exists_eq_ciInf_of_finite
  exact ⟨(a.1 : M), a.1.property, a.property, ha.trans_le hmin⟩

end KServerConj
end PaperFile010

section PaperFile011
set_option autoImplicit false

namespace KServerConj

theorem eq_2 {M : Type*} [PseudoMetricSpace M] [DecidableEq M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) :
    (∀ X : Finset M, X.card = k → workFn k C₀ r 0 X = confDist C₀ X) ∧
    ∀ t : ℕ, 1 ≤ t → ∀ X : Finset M, X.card = k →
      (∀ x ∈ X, (r t ∉ X ∨ x = r t) →
        workFn k C₀ r t X ≤ workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x) ∧
      ∃ x ∈ X, (r t ∉ X ∨ x = r t) ∧
        workFn k C₀ r t X = workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x := by
  exact ⟨fun X _ => workFn_zero k C₀ r X, fun t ht X hX =>
    ⟨fun x hx hvalid => workFn_rec_le k hk C₀ hC₀ r t ht X hX x hx hvalid,
      (workFn_rec_ge k hk C₀ hC₀ r t ht X hX).elim
        (fun x ⟨hx, hvalid, hge⟩ => ⟨x, hx, hvalid,
          le_antisymm (workFn_rec_le k hk C₀ hC₀ r t ht X hX x hx hvalid) hge⟩)⟩⟩

end KServerConj
end PaperFile011

section PaperFile012
namespace KServerConj

theorem workFn_map_compat {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) (hd : ∀ x y, dist (f x) (f y) = dist x y)
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset N) (hC₀ : C₀.card = k)
    (rN : ℕ → N) (rM : ℕ → M) (T : ℕ)
    (hreq : ∀ t, 1 ≤ t → t ≤ T → f (rN t) = rM t) :
    ∀ t, t ≤ T → ∀ X : Finset N, X.card = k →
      workFn k (C₀.map f) rM t (X.map f) = workFn k C₀ rN t X := by
  classical
  have hC₀M : (C₀.map f).card = k := by simpa only [Finset.card_map] using hC₀
  intro t
  induction t with
  | zero =>
    intro _hT X hX
    simpa only [workFn_zero] using confDist_map_embedding f hd C₀ X (hC₀.trans hX.symm)
  | succ n ih =>
    intro hn X hX
    have hr := hreq (n + 1) (by omega) hn
    have hXM : (X.map f).card = k := by simpa only [Finset.card_map] using hX
    have hcost (x : N) (hx : x ∈ X) (hvalid : rN (n + 1) ∉ X ∨ x = rN (n + 1)) :
        workFn k (C₀.map f) rM n (insert (rM (n + 1)) ((X.map f).erase (f x))) +
          dist (rM (n + 1)) (f x) =
        workFn k C₀ rN n (insert (rN (n + 1)) (X.erase x)) + dist (rN (n + 1)) x := by
      have hY := (card_insert_erase_admissible X x hx (rN (n + 1)) hvalid).trans hX
      have hm : (insert (rN (n + 1)) (X.erase x)).map f =
          insert (rM (n + 1)) ((X.map f).erase (f x)) := by
        simp only [Finset.map_insert, Finset.map_erase, hr]
      rw [← hm, ih ((Nat.le_succ n).trans hn) _ hY, ← hr, hd]
    apply le_antisymm
    · obtain ⟨x, hx, hvalid, hrec⟩ := ((eq_2 k hk C₀ hC₀ rN).2 (n + 1) (by omega) X hX).2
      have hmvalid : rM (n + 1) ∉ X.map f ∨ f x = rM (n + 1) := by
        simpa only [← hr, Finset.mem_map', f.injective.eq_iff] using hvalid
      have hle := workFn_rec_le k hk (C₀.map f) hC₀M rM (n + 1) (by omega)
        (X.map f) hXM (f x) (Finset.mem_map_of_mem f hx) hmvalid
      simp only [Nat.add_sub_cancel] at hle hrec
      exact hle.trans_eq ((hcost x hx hvalid).trans hrec.symm)
    · obtain ⟨y, hy, hvalid, hrec⟩ :=
        ((eq_2 k hk (C₀.map f) hC₀M rM).2 (n + 1) (by omega) (X.map f) hXM).2
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      have hnvalid : rN (n + 1) ∉ X ∨ x = rN (n + 1) := by
        simpa only [← hr, Finset.mem_map', f.injective.eq_iff] using hvalid
      have hle := workFn_rec_le k hk C₀ hC₀ rN (n + 1) (by omega) X hX x hx hnvalid
      simp only [Nat.add_sub_cancel] at hle hrec
      exact hle.trans_eq ((hcost x hx hnvalid).symm.trans hrec.symm)

end KServerConj
end PaperFile012

section PaperFile014
open scoped BigOperators

namespace KServerConj

def finsetInclusion {M : Type*} (G : Finset M) : G ↪ M := Function.Embedding.subtype _

noncomputable def restrictConfig {M : Type*} (G X : Finset M) : Finset G := by
  classical
  exact Finset.univ.filter (fun x : G => (x : M) ∈ X)

@[simp] theorem mem_restrictConfig {M : Type*} (G X : Finset M) (x : G) :
    x ∈ restrictConfig G X ↔ (x : M) ∈ X := by
  classical
  simp [restrictConfig]

theorem map_restrictConfig {M : Type*} (G X : Finset M) (hX : X ⊆ G) :
    (restrictConfig G X).map (finsetInclusion G) = X := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_restrictConfig G X y).mp hy
  · intro hx
    exact Finset.mem_map.mpr ⟨⟨x, hX hx⟩, (mem_restrictConfig G X _).mpr hx, rfl⟩

theorem card_restrictConfig {M : Type*} (G X : Finset M) (hX : X ⊆ G) :
    (restrictConfig G X).card = X.card := by
  simpa only [Finset.card_map] using congrArg Finset.card (map_restrictConfig G X hX)

theorem finsetInclusion_dist {M : Type*} [PseudoMetricSpace M] (G : Finset M) (x y : G) :
    dist (finsetInclusion G x) (finsetInclusion G y) = dist x y := rfl

theorem IsWFATraj.toSchedule {M : Type*} [PseudoMetricSpace M]
    {k T : ℕ} {C₀ : Finset M} {r : ℕ → M} {C : ℕ → Finset M}
    (hC : IsWFATraj k C₀ r T C) : IsSchedule k C₀ r T C := by
  exact ⟨hC.1, fun t ht hT => ⟨(hC.2 t ht hT).1, (hC.2 t ht hT).2.1⟩⟩

theorem wfaCost_map_compat {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) (hd : ∀ x y, dist (f x) (f y) = dist x y)
    (k T : ℕ) (CN : ℕ → Finset N) (CM : ℕ → Finset M)
    (hcard : ∀ t, t ≤ T → (CN t).card = k)
    (hmap : ∀ t, t ≤ T → (CN t).map f = CM t) : wfaCost CN T = wfaCost CM T := by
  unfold wfaCost
  apply Finset.sum_congr rfl
  intro t ht
  have hT : t ≤ T := (Finset.mem_Icc.mp ht).2
  have hp : t - 1 ≤ T := (Nat.sub_le t 1).trans hT
  have he := confDist_map_embedding f hd (CN (t - 1)) (CN t)
    ((hcard (t - 1) hp).trans (hcard t hT).symm)
  rw [hmap (t - 1) hp, hmap t hT] at he
  exact he.symm

theorem IsSchedule.pullback {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) {k T : ℕ} {C₀N : Finset N} {C₀M : Finset M}
    {rN : ℕ → N} {rM : ℕ → M} {SN : ℕ → Finset N} {SM : ℕ → Finset M}
    (h₀ : C₀N.map f = C₀M)
    (hreq : ∀ t, 1 ≤ t → t ≤ T → f (rN t) = rM t)
    (hmap : ∀ t, t ≤ T → (SN t).map f = SM t)
    (hS : IsSchedule k C₀M rM T SM) : IsSchedule k C₀N rN T SN := by
  refine ⟨Finset.map_injective f ((hmap 0 (Nat.zero_le T)).trans (hS.1.trans h₀.symm)), ?_⟩
  intro t ht hT
  have hs := hS.2 t ht hT
  refine ⟨?_, ?_⟩
  · simpa only [Finset.card_map] using (congrArg Finset.card (hmap t hT)).trans hs.1
  · apply (Finset.mem_map' f).mp
    rw [hmap t hT, hreq t ht hT]
    exact hs.2

theorem IsWFATraj.pullback {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) (hd : ∀ x y, dist (f x) (f y) = dist x y)
    {k T : ℕ} (hk : 1 ≤ k) {C₀N : Finset N} {C₀M : Finset M}
    (hC₀N : C₀N.card = k) {rN : ℕ → N} {rM : ℕ → M}
    {CN : ℕ → Finset N} {CM : ℕ → Finset M}
    (h₀ : C₀N.map f = C₀M)
    (hreq : ∀ t, 1 ≤ t → t ≤ T → f (rN t) = rM t)
    (hmap : ∀ t, t ≤ T → (CN t).map f = CM t)
    (hC : IsWFATraj k C₀M rM T CM) : IsWFATraj k C₀N rN T CN := by
  classical
  have hS := IsSchedule.pullback f h₀ hreq hmap hC.toSchedule
  refine ⟨hS.1, ?_⟩
  intro t ht hT
  have hs := hS.2 t ht hT
  refine ⟨hs.1, hs.2, ?_⟩
  intro Y hY hrY
  have hYm : (Y.map f).card = k := by simpa only [Finset.card_map] using hY
  have hrYm : rM t ∈ Y.map f := by
    rw [← hreq t ht hT]
    exact Finset.mem_map_of_mem f hrY
  have hle := (hC.2 t ht hT).2.2 (Y.map f) hYm hrYm
  have hprev : (CN (t - 1)).card = k := hS.card hC₀N (t - 1) ((Nat.sub_le t 1).trans hT)
  have hwC := workFn_map_compat f hd k hk C₀N hC₀N rN rM T hreq t hT (CN t) hs.1
  have hwY := workFn_map_compat f hd k hk C₀N hC₀N rN rM T hreq t hT Y hY
  have hdC := confDist_map_embedding f hd (CN (t - 1)) (CN t) (hprev.trans hs.1.symm)
  have hdY := confDist_map_embedding f hd (CN (t - 1)) Y (hprev.trans hY.symm)
  rw [h₀, hmap t hT] at hwC
  rw [h₀] at hwY
  rw [hmap (t - 1) ((Nat.sub_le t 1).trans hT), hmap t hT] at hdC
  rw [hmap (t - 1) ((Nat.sub_le t 1).trans hT)] at hdY
  simpa only [hwC, hwY, hdC, hdY] using hle

end KServerConj
end PaperFile014

section PaperFile016
open scoped BigOperators

namespace KServerConj

theorem opt_costs_bdd {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (T : ℕ) :
    BddBelow {c : ℝ | ∃ S : ℕ → Finset M, IsSchedule k C₀ r T S ∧ c = wfaCost S T} := by
  exact ⟨0, fun _ ⟨S, _, hc⟩ => hc.symm ▸ Finset.sum_nonneg
    (fun _ _ => confDist_nonneg_all _ _)⟩

theorem opt_costs_nonempty {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) :
    {c : ℝ | ∃ S : ℕ → Finset M, IsSchedule k C₀ r T S ∧ c = wfaCost S T}.Nonempty := by
  exact (exists_schedule k hk C₀ hC₀ r T).elim (fun S hS => ⟨_, S, hS, rfl⟩)

theorem opt_le_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (T : ℕ)
    (S : ℕ → Finset M) (hS : IsSchedule k C₀ r T S) : opt k C₀ r T ≤ wfaCost S T := by
  exact csInf_le (opt_costs_bdd k C₀ r T) ⟨S, hS, rfl⟩

theorem opt_approx_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : ℕ → Finset M, IsSchedule k C₀ r T S ∧ wfaCost S T ≤ opt k C₀ r T + ε := by
  obtain ⟨c, ⟨S, hS, rfl⟩, hc⟩ := exists_lt_of_csInf_lt
    (opt_costs_nonempty k hk C₀ hC₀ r T) (lt_add_of_pos_right (opt k C₀ r T) hε)
  exact ⟨S, hS, hc.le⟩

theorem opt_le_workFn {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ)
    (X : Finset M) : opt k C₀ r T ≤ workFn k C₀ r T X := by
  apply le_csInf (workFn_costs_nonempty k C₀ r T X (exists_schedule k hk C₀ hC₀ r T))
  rintro c ⟨S, hS, rfl⟩
  exact (opt_le_schedule k C₀ r T S hS).trans
    (le_add_of_nonneg_right (confDist_nonneg_all _ _))

theorem min_workFn_eq_opt {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ)
    (XT : Finset M) (hmin : ∀ X : Finset M, X.card = k → workFn k C₀ r T XT ≤ workFn k C₀ r T X) :
    workFn k C₀ r T XT = opt k C₀ r T := by
  apply le_antisymm ?_ (opt_le_workFn k hk C₀ hC₀ r T XT)
  apply le_csInf (opt_costs_nonempty k hk C₀ hC₀ r T)
  rintro c ⟨S, hS, rfl⟩
  have hb := workFn_le_schedule k C₀ r T (S T) S hS
  simp only [confDist_self, add_zero] at hb
  exact (hmin (S T) (hS.card hC₀ T le_rfl)).trans hb

theorem exists_workFn_minimizer {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) :
    ∃ XT : Finset M, XT.card = k ∧
      (∀ X : Finset M, X.card = k → workFn k C₀ r T XT ≤ workFn k C₀ r T X) ∧
      workFn k C₀ r T XT = opt k C₀ r T := by
  classical
  let A := {X : Finset M // X.card = k}
  let : Nonempty A := ⟨⟨C₀, hC₀⟩⟩
  let f (X : A) := workFn k C₀ r T X.1
  have hfb : BddBelow (Set.range f) :=
    ⟨0, fun _ ⟨X, hX⟩ => hX ▸ workFn_nonneg k hk C₀ hC₀ r T X.1⟩
  obtain ⟨XT, hXT⟩ : ∃ X : A, f X = ⨅ X : A, f X := exists_eq_ciInf_of_finite
  have hmin (X : Finset M) (hX : X.card = k) : workFn k C₀ r T XT.1 ≤ workFn k C₀ r T X :=
    hXT.trans_le (ciInf_le hfb (⟨X, hX⟩ : A))
  exact ⟨XT.1, XT.2, hmin, min_workFn_eq_opt k hk C₀ hC₀ r T XT.1 hmin⟩

end KServerConj
end PaperFile016

section PaperFile018
open scoped BigOperators

namespace KServerConj

private theorem paperFile018_sum_offDiag_dist_for_map {M : Type*} [PseudoMetricSpace M] (X : Finset M) :
    (∑ p ∈ X.offDiag, dist p.1 p.2) = ∑ i ∈ X, ∑ j ∈ X, dist i j := by
  classical
  calc
    _ = ∑ p ∈ X ×ˢ X, dist p.1 p.2 := by
      apply Finset.sum_subset
      · intro p hp
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_offDiag.mp hp).1, (Finset.mem_offDiag.mp hp).2.1⟩
      · intro p hp hn
        have heq : p.1 = p.2 := by
          by_contra h
          exact hn (Finset.mem_offDiag.mpr
            ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2, h⟩)
        simp only [heq, dist_self]
    _ = _ := Finset.sum_product X X (fun p => dist p.1 p.2)

theorem cl_map {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) (hf : ∀ x y, dist (f x) (f y) = dist x y) (X : Finset N) :
    cl (X.map f) = cl X := by
  classical
  unfold cl
  rw [paperFile018_sum_offDiag_dist_for_map, paperFile018_sum_offDiag_dist_for_map]
  simp only [Finset.sum_map, hf]

theorem cl_nonneg {M : Type*} [PseudoMetricSpace M] (X : Finset M) : 0 ≤ cl X := by
  classical
  unfold cl
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg)) zero_le_two

end KServerConj
end PaperFile018

section PaperFile019
open scoped BigOperators

namespace KServerConj

theorem finite_subspace_bound_implies_bound {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k)
    (hfinite : ∀ (G : Finset M) (A : Finset G), A.card = k →
      ∀ (q : ℕ → G) (T : ℕ) (D : ℕ → Finset G), IsWFATraj k A q T D →
        wfaCost D T ≤ (k : ℝ) * opt k A q T + cl A)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ)
    (C : ℕ → Finset M) (hC : IsWFATraj k C₀ r T C) :
    wfaCost C T ≤ (k : ℝ) * opt k C₀ r T + cl C₀ := by
  classical
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S, hS, hcostS⟩ := opt_approx_schedule k hk C₀ hC₀ r T
    (ε / (k : ℝ)) (div_pos hε hkR)
  let G : Finset M := C₀ ∪ ((Finset.range (T + 1)).biUnion C ∪
    (Finset.range (T + 1)).biUnion S)
  have hG₀ : C₀ ⊆ G := fun x hx => Finset.mem_union_left _ hx
  have hGC (t : ℕ) (ht : t ≤ T) : C t ⊆ G := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht), hx⟩))
  have hGS (t : ℕ) (ht : t ≤ T) : S t ⊆ G := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht), hx⟩))
  obtain ⟨p, hp⟩ : C₀.Nonempty := Finset.card_pos.mp (by omega)
  let A : Finset G := restrictConfig G C₀
  let CN : ℕ → Finset G := fun t => restrictConfig G (C t)
  let SN : ℕ → Finset G := fun t => restrictConfig G (S t)
  let q : ℕ → G := fun t => if h : r t ∈ G then ⟨r t, h⟩ else ⟨p, hG₀ hp⟩
  have hAmap : A.map (finsetInclusion G) = C₀ := map_restrictConfig G C₀ hG₀
  have hA : A.card = k := (card_restrictConfig G C₀ hG₀).trans hC₀
  have hCNmap (t : ℕ) (ht : t ≤ T) : (CN t).map (finsetInclusion G) = C t :=
    map_restrictConfig G (C t) (hGC t ht)
  have hSNmap (t : ℕ) (ht : t ≤ T) : (SN t).map (finsetInclusion G) = S t :=
    map_restrictConfig G (S t) (hGS t ht)
  have hq (t : ℕ) (ht : 1 ≤ t) (hT : t ≤ T) : finsetInclusion G (q t) = r t := by
    have hr : r t ∈ G := hGC t hT ((hC.2 t ht hT).2.1)
    simp only [q, dif_pos hr]
    rfl
  have hCN : IsWFATraj k A q T CN :=
    IsWFATraj.pullback (finsetInclusion G) (finsetInclusion_dist G) hk hA hAmap hq hCNmap hC
  have hSN : IsSchedule k A q T SN :=
    IsSchedule.pullback (finsetInclusion G) hAmap hq hSNmap hS
  have hcostCN : wfaCost CN T = wfaCost C T := wfaCost_map_compat
    (finsetInclusion G) (finsetInclusion_dist G) k T CN C
    (fun t ht => hCN.toSchedule.card hA t ht) hCNmap
  have hcostSN : wfaCost SN T = wfaCost S T := wfaCost_map_compat
    (finsetInclusion G) (finsetInclusion_dist G) k T SN S
    (fun t ht => hSN.card hA t ht) hSNmap
  have hcl : cl A = cl C₀ := by
    rw [← hAmap, cl_map (finsetInclusion G) (finsetInclusion_dist G)]
  have hb := hfinite G A hA q T CN hCN
  have ho := opt_le_schedule k A q T SN hSN
  rw [hcostCN, hcl] at hb
  rw [hcostSN] at ho
  calc
    wfaCost C T ≤ (k : ℝ) * (opt k C₀ r T + ε / (k : ℝ)) + cl C₀ :=
      hb.trans (add_le_add (mul_le_mul_of_nonneg_left (ho.trans hcostS) hkR.le) le_rfl)
    _ = (k : ℝ) * opt k C₀ r T + cl C₀ + ε := by
      rw [mul_add, mul_div_cancel₀ _ hkR.ne']
      ring

end KServerConj
end PaperFile019

section PaperFile020
namespace KServerConj

theorem configuration_eq_singleton {M : Type*} (X : Finset M)
    (hX : X.card = 1) (r : M) (hr : r ∈ X) : X = {r} := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hX
  have he : r = x := by simpa only [hx, Finset.mem_singleton] using hr
  simpa only [← he] using hx

theorem one_server_schedules_eq {M : Type*} [PseudoMetricSpace M]
    (C₀ : Finset M) (r : ℕ → M) (T : ℕ)
    (C S : ℕ → Finset M) (hC : IsSchedule 1 C₀ r T C) (hS : IsSchedule 1 C₀ r T S)
    (t : ℕ) (ht : t ≤ T) : C t = S t := by
  by_cases hzero : t = 0
  · subst t
    exact hC.1.trans hS.1.symm
  · have hpos : 1 ≤ t := by omega
    exact (configuration_eq_singleton (C t) (hC.2 t hpos ht).1 (r t)
      (hC.2 t hpos ht).2).trans
        (configuration_eq_singleton (S t) (hS.2 t hpos ht).1 (r t) (hS.2 t hpos ht).2).symm

theorem one_server_schedule_cost_eq {M : Type*} [PseudoMetricSpace M]
    (C₀ : Finset M) (r : ℕ → M) (T : ℕ)
    (C S : ℕ → Finset M) (hC : IsSchedule 1 C₀ r T C) (hS : IsSchedule 1 C₀ r T S) :
    wfaCost C T = wfaCost S T := by
  unfold wfaCost
  apply Finset.sum_congr rfl
  intro t ht
  have hT := (Finset.mem_Icc.mp ht).2
  rw [one_server_schedules_eq C₀ r T C S hC hS t hT,
    one_server_schedules_eq C₀ r T C S hC hS (t - 1) ((Nat.sub_le t 1).trans hT)]

theorem one_server_cost_eq_opt {M : Type*} [PseudoMetricSpace M]
    (C₀ : Finset M) (hC₀ : C₀.card = 1) (r : ℕ → M) (T : ℕ)
    (C : ℕ → Finset M) (hC : IsSchedule 1 C₀ r T C) :
    wfaCost C T = opt 1 C₀ r T := by
  apply le_antisymm ?_ (opt_le_schedule 1 C₀ r T C hC)
  apply le_csInf (opt_costs_nonempty 1 le_rfl C₀ hC₀ r T)
  rintro c ⟨S, hS, rfl⟩
  exact (one_server_schedule_cost_eq C₀ r T C S hC hS).le

theorem one_server_wfa_bound {M : Type*} [PseudoMetricSpace M]
    (C₀ : Finset M) (hC₀ : C₀.card = 1) (r : ℕ → M) (T : ℕ)
    (C : ℕ → Finset M) (hC : IsWFATraj 1 C₀ r T C) :
    wfaCost C T ≤ (1 : ℝ) * opt 1 C₀ r T + cl C₀ := by
  rw [one_server_cost_eq_opt C₀ hC₀ r T C hC.toSchedule, one_mul]
  exact le_add_of_nonneg_right (cl_nonneg C₀)

end KServerConj
end PaperFile020

section PaperFile021
namespace KServerConj

theorem workFn_objective_lower {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ)
    (A Y : Finset M) (hA : A.card = k) (hY : Y.card = k) :
    workFn k C₀ r t A ≤ workFn k C₀ r t Y + confDist A Y := by
  simpa only [confDist_symm Y A (hY.trans hA.symm)] using
    workFn_lipschitz k hk C₀ hC₀ r t Y A hY hA

theorem exists_wfa_minimizer {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (A : Finset M) (hA : A.card = k) :
    ∃ Y : Finset M, Y.card = k ∧ r t ∈ Y ∧
      workFn k C₀ r t Y + confDist A Y = workFn k C₀ r t A := by
  obtain ⟨x, hx, hvalid, hrec⟩ := ((eq_2 k hk C₀ hC₀ r).2 t ht A hA).2
  let Y := insert (r t) (A.erase x)
  have hY : Y.card = k := (card_insert_erase_admissible A x hx (r t) hvalid).trans hA
  have hrY : r t ∈ Y := Finset.mem_insert_self _ _
  have hcover := workFn_covered k hk C₀ hC₀ r t ht Y hY hrY
  have hD : confDist A Y ≤ dist (r t) x := by
    rw [confDist_symm A Y (hA.trans hY.symm)]
    exact confDist_insert_erase_le A x hx (r t) hvalid
  have hupper : workFn k C₀ r t Y + confDist A Y ≤ workFn k C₀ r t A := by
    rw [hcover, hrec]
    exact add_le_add le_rfl hD
  exact ⟨Y, hY, hrY, le_antisymm hupper (workFn_objective_lower k hk C₀ hC₀ r t A Y hA hY)⟩

theorem IsWFATraj.card {M : Type*} [PseudoMetricSpace M] {k T : ℕ} {C₀ : Finset M}
    {r : ℕ → M} {C : ℕ → Finset M} (hC : IsWFATraj k C₀ r T C) (hC₀ : C₀.card = k)
    (t : ℕ) (ht : t ≤ T) : (C t).card = k := by
  by_cases hz : t = 0
  · simpa only [hz, hC.1] using hC₀
  · exact (hC.2 t (Nat.one_le_iff_ne_zero.mpr hz) ht).1

theorem IsWFATraj.mono {M : Type*} [PseudoMetricSpace M] {k T U : ℕ} {C₀ : Finset M}
    {r : ℕ → M} {C : ℕ → Finset M} (hC : IsWFATraj k C₀ r T C) (hUT : U ≤ T) :
    IsWFATraj k C₀ r U C := by
  exact ⟨hC.1, fun t ht htU => hC.2 t ht (htU.trans hUT)⟩

theorem IsWFATraj.objective_eq {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (T : ℕ) (C : ℕ → Finset M) (hC : IsWFATraj k C₀ r T C)
    (t : ℕ) (ht : 1 ≤ t) (hT : t ≤ T) :
    workFn k C₀ r t (C t) + confDist (C (t - 1)) (C t) = workFn k C₀ r t (C (t - 1)) := by
  classical
  have hprev := hC.card hC₀ (t - 1) ((Nat.sub_le t 1).trans hT)
  have hcur := hC.2 t ht hT
  obtain ⟨Y, hY, hrY, heq⟩ := exists_wfa_minimizer k hk C₀ hC₀ r t ht (C (t - 1)) hprev
  exact le_antisymm ((hcur.2.2 Y hY hrY).trans_eq heq)
    (workFn_objective_lower k hk C₀ hC₀ r t (C (t - 1)) (C t) hprev hcur.1)

end KServerConj
end PaperFile021

section PaperFile022
namespace KServerConj

theorem exists_wfa_trajectory {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) :
    ∃ C : ℕ → Finset M, IsWFATraj k C₀ r T C := by
  classical
  let Config := {X : Finset M // X.card = k}
  let start : Config := ⟨C₀, hC₀⟩
  let next (n : ℕ) (A : Config) : Config :=
    ⟨(exists_wfa_minimizer k hk C₀ hC₀ r (n + 1) (by omega) A.1 A.2).choose,
      (exists_wfa_minimizer k hk C₀ hC₀ r (n + 1) (by omega) A.1 A.2).choose_spec.1⟩
  let states : ℕ → Config := Nat.rec start next
  let C : ℕ → Finset M := fun t => (states t).1
  refine ⟨C, rfl, ?_⟩
  intro t ht _hT
  cases t with
  | zero => omega
  | succ n =>
    have hstep := (exists_wfa_minimizer k hk C₀ hC₀ r (n + 1) (by omega)
      (states n).1 (states n).2).choose_spec
    exact ⟨hstep.1, hstep.2.1, fun Y hY _hrY =>
      hstep.2.2.trans_le
        (workFn_objective_lower k hk C₀ hC₀ r (n + 1) (states n).1 Y (states n).2 hY)⟩

end KServerConj
end PaperFile022

section PaperFile023
namespace KServerConj

theorem arbitrary_space_theorem_of_finite_bound {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k)
    (hfinite : 2 ≤ k → ∀ (G : Finset M) (A : Finset G), A.card = k →
      ∀ (q : ℕ → G) (T : ℕ) (D : ℕ → Finset G), IsWFATraj k A q T D →
        wfaCost D T ≤ (k : ℝ) * opt k A q T + cl A)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) :
    (∃ C : ℕ → Finset M, IsWFATraj k C₀ r T C) ∧
    ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
      wfaCost C T ≤ (k : ℝ) * opt k C₀ r T + cl C₀ := by
  refine ⟨exists_wfa_trajectory k hk C₀ hC₀ r T, ?_⟩
  intro C hC
  by_cases hkone : k = 1
  · have hcardone : C₀.card = 1 := hC₀.trans hkone
    have hCone : IsWFATraj 1 C₀ r T C := hkone ▸ hC
    simpa only [hkone, Nat.cast_one] using one_server_wfa_bound C₀ hcardone r T C hCone
  · exact finite_subspace_bound_implies_bound k hk (hfinite (by omega)) C₀ hC₀ r T C hC

end KServerConj
end PaperFile023

section PaperFile024
set_option autoImplicit false

namespace KServerConj

theorem finite_wfa_bound_of_endpoint {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ)
    (hendpoint : ∀ XT : Finset M, XT.card = k →
      (∀ X : Finset M, X.card = k → workFn k C₀ r T XT ≤ workFn k C₀ r T X) →
      ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
        wfaCost C T ≤ (k : ℝ) * workFn k C₀ r T XT + cl C₀ - cl XT) :
    ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
      wfaCost C T ≤ (k : ℝ) * opt k C₀ r T + cl C₀ := by
  classical
  intro C hC
  obtain ⟨XT, hXT, hmin, hopt⟩ := exists_workFn_minimizer k hk C₀ hC₀ r T
  have hbound := hendpoint XT hXT hmin C hC
  rw [hopt] at hbound
  exact hbound.trans (sub_le_self _ (cl_nonneg XT))

end KServerConj
end PaperFile024

section PaperFile025
open scoped BigOperators

namespace KServerConj

theorem payment_telescope (e : ℕ → ℝ) (Φ : ℕ → WithTop ℝ) (T : ℕ)
    (hstep : ∀ t, 1 ≤ t → t ≤ T → (e t : WithTop ℝ) + Φ (t - 1) ≤ Φ t) :
    ((∑ t ∈ Finset.Icc 1 T, e t : ℝ) : WithTop ℝ) + Φ 0 ≤ Φ T := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hp := ih (fun t ht htT => hstep t ht (htT.trans (Nat.le_succ T)))
    have hs := hstep (T + 1) (Nat.succ_le_succ (Nat.zero_le T)) le_rfl
    calc
      _ = (e (T + 1) : WithTop ℝ) +
          (((∑ t ∈ Finset.Icc 1 T, e t : ℝ) : WithTop ℝ) + Φ 0) := by
        rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le T)), WithTop.coe_add]
        ac_rfl
      _ ≤ (e (T + 1) : WithTop ℝ) + Φ T := add_le_add le_rfl hp
      _ ≤ Φ (T + 1) := by simpa only [Nat.add_sub_cancel] using hs

end KServerConj
end PaperFile025

section PaperFile030
open scoped BigOperators

theorem det_mul_det_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (j : ι) (v : ι → R) :
    A.det * (B.updateCol j v).det =
      ∑ i, (A.updateCol i v).det *
        (B.updateCol j (fun r => A r i)).det := by
  have h : A.det • v =
      ∑ i, (A.updateCol i v).det • (fun r => A r i) := by
    rw [← Matrix.mulVec_cramer A v]
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.cramer_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have h' := congrArg (fun w : ι → R => B.cramer w j) h
  simp only [map_smul, map_sum] at h'
  simpa only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cramer_apply] using h'
end PaperFile030

section PaperFile031
open scoped BigOperators

namespace DetValuationMilestone

def prependColumn {n : ℕ} {R : Type*} (v : Fin (n + 1) → R)
    (W : Matrix (Fin (n + 1)) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun r j => Fin.cases (v r) (fun j => W r j) j

theorem updateCol_prepend {n : ℕ} {R : Type*}
    (v w : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn v W).updateCol 0 w = prependColumn w W := by
  ext r j
  cases j using Fin.cases <;> simp [prependColumn, Matrix.updateCol]

theorem det_prepend_single {n : ℕ} {R : Type*} [CommRing R]
    (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (Pi.single 0 1) W).det = (W.submatrix Fin.succ id).det := by
  rw [Matrix.det_succ_column_zero]
  simp [prependColumn, Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]

theorem det_mul_det_prepend {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    A.det * (prependColumn v W).det =
      ∑ i, (A.updateCol i v).det * (prependColumn (fun r => A r i) W).det := by
  simpa only [updateCol_prepend] using det_mul_det_updateCol A (prependColumn v W) 0 v

theorem det_prepend_smul {n : ℕ} {R : Type*} [CommRing R]
    (c : R) (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (c • v) W).det = c * (prependColumn v W).det := by
  simpa only [updateCol_prepend] using Matrix.det_updateCol_smul (prependColumn v W) 0 c v

theorem prepend_submatrix {n : ℕ} {R ι : Type*}
    (H : Matrix (Fin (n + 1)) ι R) (x : ι) (y : Fin n → ι) :
    prependColumn (fun r => H r x) (H.submatrix id y) =
      H.submatrix id (Fin.cases x y) := by
  ext r j
  cases j using Fin.cases <;> rfl

theorem projected_minor_identity {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (y : Fin n → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det * (H.submatrix Fin.succ y).det =
      ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i *
        (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det := by
  simpa only [det_prepend_single, Matrix.submatrix_submatrix, Function.comp_id,
    Function.id_comp, hcol, det_prepend_smul, mul_assoc] using
      det_mul_det_prepend A (Pi.single 0 1) (H.submatrix id y)

theorem exists_nonzero_projected_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (H : Matrix (Fin (n + 1)) ι R) (x : Fin (n + 1) → ι)
    (hdet : (H.submatrix id x).det ≠ 0) :
    ∃ y : Fin n → ι, (H.submatrix Fin.succ y).det ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hdet
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [Matrix.submatrix_submatrix, Function.id_comp, h, mul_zero]

theorem nonzero_unscaled_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) : (H.submatrix id x).det ≠ 0 := by
  have hA : A = Matrix.of (fun r i => c i * (H.submatrix id x) r i) :=
    funext fun r => funext fun i => congrFun (hcol i) r
  rw [hA, Matrix.det_mul_row c (H.submatrix id x)] at hdet
  exact right_ne_zero_of_mul hdet

theorem det_eq_sum_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det = ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i * H 0 (x i) := by
  have hentry : ∀ r i, A r i = c i * H r (x i) :=
    fun r i => congrFun (hcol i) r
  simpa [Matrix.mulVec, dotProduct, Matrix.cramer_apply, hentry,
    mul_comm, mul_left_comm, mul_assoc] using
      (congrFun (Matrix.mulVec_cramer A (Pi.single 0 1)) 0).symm

theorem exists_nonzero_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ i, (A.updateCol i (Pi.single 0 1)).det * c i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hdet (by
    simpa only [h, zero_mul, Finset.sum_const_zero] using det_eq_sum_scaled_cramer A H x c hcol)

end DetValuationMilestone
end PaperFile031

section PaperFile032
open scoped BigOperators

namespace DetValuationMilestone

theorem valuation_sum_lower_bound
    {R ι : Type*} [AddCommMonoid R]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (s : Finset ι) (f : ι → R) (c : WithTop ℝ)
    (hf : ∀ i ∈ s, c ≤ ν (f i)) :
    c ≤ ν (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))).trans (hadd _ _)

theorem valuation_lower_bound_of_minor_identity
    {R ι : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D P : R) (a M : ι → R) (δ α μ : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : D * P = ∑ i, a i * M i)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i, (μ : WithTop ℝ) ≤ ν (M i)) :
    ((α + μ - δ : ℝ) : WithTop ℝ) ≤ ν P := by
  have hsum : ((α + μ : ℝ) : WithTop ℝ) ≤ ν (∑ i, a i * M i) := by
    apply valuation_sum_lower_bound ν hzero hadd
    intro i _
    simpa only [WithTop.coe_add, hmul] using add_le_add (ha i) (hM i)
  rw [← hid, hmul, hD] at hsum
  apply WithTop.le_of_add_le_add_left (x := (δ : WithTop ℝ)) (by simp)
  simpa only [← WithTop.coe_add,
    show δ + (α + μ - δ) = α + μ by linarith] using hsum

theorem minValue_growth_of_minor_identities
    {R ι κ : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (M : ι → κ → R)
    (δ α μ μhat : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i y, (μ : WithTop ℝ) ≤ ν (M i y))
    (hmin : ∃ y, ν (P y) = (μhat : WithTop ℝ)) :
    α - δ ≤ μhat - μ := by
  obtain ⟨y, hy⟩ := hmin
  have h := valuation_lower_bound_of_minor_identity ν hzero hmul hadd
    D (P y) a (fun i => M i y) δ α μ hD (hid y) ha (fun i => hM i y)
  rw [hy, WithTop.coe_le_coe] at h
  linarith

theorem exists_real_minimum_of_nonzero
    {R ι : Type*} [Zero R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (f : ι → R) (hnonzero : ∃ i, f i ≠ 0) :
    ∃ μ : ℝ,
      (Finset.univ.inf fun i => ν (f i)) = (μ : WithTop ℝ) ∧
      (∀ i, (μ : WithTop ℝ) ≤ ν (f i)) ∧
      (∃ i, ν (f i) = (μ : WithTop ℝ) ∧ f i ≠ 0) := by
  classical
  obtain ⟨i, hi⟩ := hnonzero
  have hfinite : (Finset.univ.inf fun i => ν (f i)) ≠ ⊤ := by
    exact ne_of_lt ((Finset.inf_le (Finset.mem_univ i)).trans_lt
      (lt_top_iff_ne_top.mpr fun h => hi ((htop _).mp h)))
  obtain ⟨μ, hμ⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset ι)
    ⟨i, Finset.mem_univ i⟩ (fun j => ν (f j))
  exact ⟨μ, hμ.symm, fun j => hμ.trans_le (Finset.inf_le (Finset.mem_univ j)),
    j, hj.symm.trans hμ.symm, fun hz => hfinite (hj.trans ((htop _).mpr hz))⟩

theorem canonical_minValue_growth
    {R ι κ η : Type*} [Semiring R] [Fintype ι] [Fintype κ] [Fintype η]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (F : η → R) (M : ι → κ → R)
    (hD : D ≠ 0)
    (ha_nonzero : ∃ i, a i ≠ 0)
    (hP_nonzero : ∃ y, P y ≠ 0)
    (hF_nonzero : ∃ z, F z ≠ 0)
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (hM : ∀ i y, M i y = 0 ∨ ∃ z, M i y = F z) :
    ∃ δ α μ μhat : ℝ,
      ν D = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν (a i)) = (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z => ν (F z)) = (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y => ν (P y)) = (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp (fun h => hD ((htop _).mp h))
  obtain ⟨α, hα, ha, _⟩ := exists_real_minimum_of_nonzero ν htop a ha_nonzero
  obtain ⟨μ, hμ, hF, _⟩ := exists_real_minimum_of_nonzero ν htop F hF_nonzero
  obtain ⟨μhat, hμhat, _, y, hy, _⟩ :=
    exists_real_minimum_of_nonzero ν htop P hP_nonzero
  exact ⟨δ, α, μ, μhat, hδ.symm, hα, hμ, hμhat,
    minValue_growth_of_minor_identities ν ((htop 0).mpr rfl) hmul hadd
      D a P M δ α μ μhat hδ.symm hid ha
      (fun i y => (hM i y).elim
        (fun hz => by simp [hz, (htop 0).mpr rfl])
        (fun ⟨z, hz⟩ => by simpa only [hz] using hF z))
      ⟨y, hy⟩⟩

end DetValuationMilestone
end PaperFile032

section PaperFile033
open scoped BigOperators

namespace DetValuationMilestone

theorem canonical_projected_minValue_growth
    {n : ℕ} {R ι : Type*} [CommRing R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ δ α μ μhat : ℝ,
      ν A.det = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν ((A.updateCol i (Pi.single 0 1)).det * c i)) =
        (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z : Fin (n + 1) → ι => ν (H.submatrix id z).det) =
        (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y : Fin n → ι => ν (H.submatrix Fin.succ y).det) =
        (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  exact canonical_minValue_growth ν htop hmul hadd A.det
    (fun i => (A.updateCol i (Pi.single 0 1)).det * c i)
    (fun y : Fin n → ι => (H.submatrix Fin.succ y).det)
    (fun z : Fin (n + 1) → ι => (H.submatrix id z).det)
    (fun i y => (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det)
    hdet (exists_nonzero_scaled_cramer A H x c hcol hdet)
    (exists_nonzero_projected_minor H x (nonzero_unscaled_minor A H x c hcol hdet))
    ⟨x, nonzero_unscaled_minor A H x c hcol hdet⟩
    (fun y => projected_minor_identity A H x y c hcol)
    (fun i y => Or.inr ⟨Fin.cases (x i) y,
      congrArg Matrix.det (prepend_submatrix H (x i) y)⟩)

end DetValuationMilestone
end PaperFile033

section PaperFile034
open scoped BigOperators

namespace DetValuationMilestone

noncomputable def tupleMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I → J => ν (G.submatrix id e).det

noncomputable def embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I ↪ J => ν (G.submatrix id e).det

theorem det_submatrix_eq_zero_of_not_injective
    {I J R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (G : Matrix I J R) (x : I → J) (hx : ¬ Function.Injective x) :
    (G.submatrix id x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (fun j => G r j) hij)

theorem embeddingMinorVal_le_tuple
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (G : Matrix I J R) (x : I → J) :
    embeddingMinorVal ν G ≤ ν (G.submatrix id x).det := by
  classical
  exact (Classical.em (Function.Injective x)).elim
    (fun hx => Finset.inf_le (f := fun e : I ↪ J => ν (G.submatrix id e).det)
      (Finset.mem_univ (⟨x, hx⟩ : I ↪ J)))
    (fun hx => by
      simpa only [det_submatrix_eq_zero_of_not_injective G x hx, hzero] using
        (le_top : embeddingMinorVal ν G ≤ ⊤))

theorem tupleMinorVal_eq_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (G : Matrix I J R) :
    tupleMinorVal ν G = embeddingMinorVal ν G := by
  classical
  exact le_antisymm
    (Finset.le_inf fun e _ => Finset.inf_le
      (f := fun x : I → J => ν (G.submatrix id x).det) (Finset.mem_univ (e : I → J)))
    (Finset.le_inf fun x _ => embeddingMinorVal_le_tuple ν hzero G x)

theorem add_finset_inf {ι : Type*} (a : WithTop ℝ) (s : Finset ι)
    (f : ι → WithTop ℝ) :
    a + s.inf f = s.inf (fun i => a + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, ← ih, min_add_add_left]

theorem tupleMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    tupleMinorVal ν (A * G) = ν A.det + tupleMinorVal ν G := by
  have hval : ∀ x : I → J, ν ((A * G).submatrix id x).det =
      ν A.det + ν (G.submatrix id x).det := fun x =>
    (congrArg ν (Matrix.det_mul A (G.submatrix id x))).trans (hmul _ _)
  simpa only [tupleMinorVal, hval] using
    (add_finset_inf (ν A.det) (Finset.univ : Finset (I → J))
      (fun x => ν (G.submatrix id x).det)).symm

theorem embeddingMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    embeddingMinorVal ν (A * G) = ν A.det + embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using tupleMinorVal_mul ν hmul A G

end DetValuationMilestone
end PaperFile034

section PaperFile035
namespace KServerConj

theorem minorVal_eq_embeddingMinorVal
    {F I J : Type*} [Field F] [Fintype I] [hI : DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal G = DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G := by
  classical
  cases Subsingleton.elim hI (Classical.decEq I)
  unfold minorVal DetValuationMilestone.embeddingMinorVal
  rfl

theorem minorVal_mul
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I (HahnSeries ℝ F)) (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_mul (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) (fun x y => AddValuation.map_mul _ x y) A G

end KServerConj
end PaperFile035

section PaperFile036
open scoped BigOperators

namespace KServerConj

noncomputable def quadraticMatrix {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (HahnSeries ℝ F) :=
  fun p c => Sym2.lift ⟨fun x y =>
    HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p,
    fun x y => by
      dsimp only
      rw [dist_comm, symProd_comm]⟩ c

theorem Qmat_eq_quadraticMatrix {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → K k M) : Qmat q = quadraticMatrix q := rfl

noncomputable def weightedColumns {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r : M) :
    Matrix (Fin k) M (HahnSeries ℝ F) :=
  fun i x => HahnSeries.single (-dist r x) (1 : F) * q x i

noncomputable def negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) : Sym2 (Fin k) → ℝ :=
  Sym2.lift ⟨fun i j => -dist (x i) (x j),
    fun i j => congrArg Neg.neg (dist_comm (x i) (x j))⟩

theorem quadraticMatrix_submatrix {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    (quadraticMatrix q).submatrix id (Sym2.map x) =
      Matrix.of (fun r c => HahnSeries.single (negPairDist x c) (1 : F) *
        sym2Mat (Matrix.of (fun i j => q (x j) i)) r c) := by
  funext r c
  induction c using Sym2.ind with
  | _ i j => rfl

end KServerConj
end PaperFile036

section PaperFile037
open scoped BigOperators

namespace KServerConj

@[simp] theorem symProd_apply {R : Type*} [CommRing R] {k : ℕ}
    (a b : Fin k → R) (i j : Fin k) :
    symProd a b s(i, j) =
      if i = j then a i * b i else a i * b j + a j * b i := by
  rfl

theorem symProd_add_left {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd (a + b) c = symProd a c + symProd b c := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.add_apply, symProd_apply]
    split_ifs <;> ring

theorem symProd_smul_left {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd (c • a) b = c • symProd a b := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.smul_apply, symProd_apply, smul_eq_mul]
    split_ifs <;> ring

theorem symProd_add_right {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd a (b + c) = symProd a b + symProd a c := by
  simpa only [symProd_comm] using symProd_add_left b c a

theorem symProd_smul_right {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd a (c • b) = c • symProd a b := by
  simpa only [symProd_comm] using symProd_smul_left c b a

def symProdBilin {R : Type*} [CommRing R] {k : ℕ} :
    (Fin k → R) →ₗ[R] (Fin k → R) →ₗ[R] (Sym2 (Fin k) → R) where
  toFun a :=
    { toFun := symProd a
      map_add' := symProd_add_right a
      map_smul' c b := symProd_smul_right c a b }
  map_add' a b := LinearMap.ext fun c => symProd_add_left a b c
  map_smul' c a := LinearMap.ext fun b => symProd_smul_left c a b

@[simp] theorem symProd_single_single {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) :
    symProd (Pi.single i (1 : R)) (Pi.single j (1 : R)) = Pi.single s(i, j) 1 := by
  funext p
  induction p using Sym2.ind with
  | _ l m =>
    by_cases hlm : l = m <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
      by_cases hmi : m = i <;> by_cases hmj : m = j <;>
      simp_all [symProd_apply, Pi.single_apply]

@[simp] theorem sym2Mat_col {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    (sym2Mat A).col s(i, j) = symProd (A.col i) (A.col j) := rfl

theorem sym2Mat_mulVec_symProd {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (a b : Fin k → R) :
    (sym2Mat A).mulVec (symProd a b) = symProd (A.mulVec a) (A.mulVec b) := by
  have h : (symProdBilin (R := R) (k := k)).compr₂ (sym2Mat A).mulVecLin =
      (symProdBilin (R := R) (k := k)).compl₁₂ A.mulVecLin A.mulVecLin := by
    apply (Pi.basisFun R (Fin k)).ext
    intro i
    apply (Pi.basisFun R (Fin k)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp [symProdBilin, symProd_single_single]
  exact congrArg (fun f => f a b) h

@[simp] theorem sym2Mat_one {R : Type*} [CommRing R] (k : ℕ) :
    sym2Mat (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simpa only [symProd_single_single, Matrix.one_mulVec] using
      sym2Mat_mulVec_symProd (1 : Matrix (Fin k) (Fin k) R)
        (Pi.single i 1) (Pi.single j 1)

theorem sym2Mat_mul {R : Type*} [CommRing R] {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) R) :
    sym2Mat (A * B) = sym2Mat A * sym2Mat B := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [← symProd_single_single, ← Matrix.mulVec_mulVec, sym2Mat_mulVec_symProd]

end KServerConj
end PaperFile037

section PaperFile038
namespace KServerConj

def sym2FinSuccEmbed (n : ℕ) :
    Fin (n + 1) ⊕ Sym2 (Fin n) → Sym2 (Fin (n + 1))
  | Sum.inl i => s(0, i)
  | Sum.inr p => p.map Fin.succ

theorem sym2FinSucc_top_ne_bottom (n : ℕ) (i : Fin (n + 1)) (p : Sym2 (Fin n)) :
    s((0 : Fin (n + 1)), i) ≠ p.map Fin.succ := by
  induction p using Sym2.ind with
  | _ a b =>
    simp [(Fin.succ_ne_zero a).symm, (Fin.succ_ne_zero b).symm]

theorem sym2FinSuccEmbed_injective (n : ℕ) : Function.Injective (sym2FinSuccEmbed n) := by
  intro x y h
  rcases x with i | p <;> rcases y with j | q
  · exact congrArg Sum.inl ((Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1))
  · exact False.elim (sym2FinSucc_top_ne_bottom n i q h)
  · exact False.elim (sym2FinSucc_top_ne_bottom n j p h.symm)
  · exact congrArg Sum.inr (Sym2.map.injective (Fin.succ_injective n) h)

theorem sym2FinSuccEmbed_surjective (n : ℕ) : Function.Surjective (sym2FinSuccEmbed n) := by
  intro p
  induction p using Sym2.ind with
  | _ i j =>
    cases i using Fin.cases with
    | zero => exact ⟨Sum.inl j, rfl⟩
    | succ i =>
      cases j using Fin.cases with
      | zero => exact ⟨Sum.inl i.succ, Sym2.eq_swap⟩
      | succ j => exact ⟨Sum.inr s(i, j), rfl⟩

noncomputable def sym2FinSuccEquiv (n : ℕ) :
    Sym2 (Fin (n + 1)) ≃ Fin (n + 1) ⊕ Sym2 (Fin n) :=
  (Equiv.ofBijective (sym2FinSuccEmbed n)
    ⟨sym2FinSuccEmbed_injective n, sym2FinSuccEmbed_surjective n⟩).symm

@[simp] theorem sym2FinSuccEquiv_symm_inl (n : ℕ) (i : Fin (n + 1)) :
    (sym2FinSuccEquiv n).symm (Sum.inl i) = s(0, i) := rfl

@[simp] theorem sym2FinSuccEquiv_symm_inr (n : ℕ) (p : Sym2 (Fin n)) :
    (sym2FinSuccEquiv n).symm (Sum.inr p) = p.map Fin.succ := rfl

@[simp] theorem sym2FinSuccEquiv_mk_zero (n : ℕ) (i : Fin (n + 1)) :
    sym2FinSuccEquiv n s(0, i) = Sum.inl i := by
  simpa only [sym2FinSuccEquiv_symm_inl] using
    (sym2FinSuccEquiv n).apply_symm_apply (Sum.inl i)

@[simp] theorem sym2FinSuccEquiv_map_succ (n : ℕ) (p : Sym2 (Fin n)) :
    sym2FinSuccEquiv n (p.map Fin.succ) = Sum.inr p := by
  simpa only [sym2FinSuccEquiv_symm_inr] using
    (sym2FinSuccEquiv n).apply_symm_apply (Sum.inr p)

theorem symProd_split_top {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl i)) =
      if i = 0 then a 0 * b 0 else a 0 * b i + a i * b 0 := by
  simp [symProd_apply, eq_comm]

@[simp] theorem symProd_split_top_zero {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl 0)) = a 0 * b 0 := by
  simp [symProd_apply]

theorem symProd_split_top_succ {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin n) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl i.succ)) =
      a 0 * b i.succ + a i.succ * b 0 := by
  simp [symProd_apply, (Fin.succ_ne_zero i).symm]

theorem symProd_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inr p)) =
      symProd (fun i => a i.succ) (fun i => b i.succ) p := by
  induction p using Sym2.ind with
  | _ i j =>
    simp only [sym2FinSuccEquiv_symm_inr, Sym2.map_mk, symProd_apply,
      (Fin.succ_injective n).eq_iff]

theorem symProd_e0_split_top {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm (Sum.inl i)) = h i := by
  by_cases hi : i = 0 <;> simp [hi, eq_comm]

theorem symProd_e0_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm (Sum.inr p)) = 0 := by
  induction p using Sym2.ind with
  | _ i j =>
    simp [symProd_apply]

theorem symProd_e0_split {R : Type*} [CommRing R] {n : ℕ} (h : Fin (n + 1) → R) :
    (fun p : Fin (n + 1) ⊕ Sym2 (Fin n) =>
      symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm p)) =
      Sum.elim h (fun _ => 0) := by
  exact funext (Sum.rec (symProd_e0_split_top h) (symProd_e0_split_bottom h))

end KServerConj
end PaperFile038

section PaperFile039
namespace KServerConj

@[simp] theorem quadraticMatrix_apply_pair {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F)
    (p : Sym2 (Fin k)) (x y : M) :
    quadraticMatrix q p s(x, y) =
      HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p := rfl

theorem quadraticMatrix_request_column {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) :
    (quadraticMatrix q).col s(r, x) =
      symProd (Pi.single 0 1) (fun i => weightedColumns q r i x) := by
  funext p
  change HahnSeries.single (-dist r x) (1 : F) * symProd (q r) (q x) p =
    symProd (Pi.single 0 1) (HahnSeries.single (-dist r x) (1 : F) • q x) p
  rw [hqr, symProd_smul_right]
  rfl

theorem quadraticMatrix_request_top {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) (i : Fin (n + 1)) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inl i)) s(r, x) =
      weightedColumns q r i x := by
  exact (congrFun (quadraticMatrix_request_column q r hqr x)
    ((sym2FinSuccEquiv n).symm (Sum.inl i))).trans
      (symProd_e0_split_top (fun i => weightedColumns q r i x) i)

theorem quadraticMatrix_request_bottom {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) (p : Sym2 (Fin n)) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inr p)) s(r, x) = 0 := by
  exact (congrFun (quadraticMatrix_request_column q r hqr x)
    ((sym2FinSuccEquiv n).symm (Sum.inr p))).trans
      (symProd_e0_split_bottom (fun i => weightedColumns q r i x) p)

theorem quadraticMatrix_split_bottom {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F)
    (p : Sym2 (Fin n)) (c : Sym2 M) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inr p)) c =
      quadraticMatrix (fun x (i : Fin n) => q x i.succ) p c := by
  induction c using Sym2.ind with
  | _ x y =>
    exact congrArg (fun z => HahnSeries.single (-dist x y) (1 : F) * z)
      (symProd_split_bottom (q x) (q y) p)

theorem quadraticMatrix_exists_old_minor {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : Fin (n + 1) → M)
    (y : Sym2 (Fin n) → Sym2 M) :
    ∃ c : Sym2 (Fin (n + 1)) → Sym2 M,
      ((quadraticMatrix q).submatrix id c).det =
        ((weightedColumns q r).submatrix id x).det *
          ((quadraticMatrix (fun m (i : Fin n) => q m i.succ)).submatrix id y).det := by
  let e := sym2FinSuccEquiv n
  let c : Sym2 (Fin (n + 1)) → Sym2 M :=
    fun p => Sum.elim (fun i => s(r, x i)) y (e p)
  let A := (weightedColumns q r).submatrix id x
  let D := (quadraticMatrix (fun m (i : Fin n) => q m i.succ)).submatrix id y
  let B : Matrix (Fin (n + 1)) (Sym2 (Fin n)) (HahnSeries ℝ F) :=
    fun i j => quadraticMatrix q (e.symm (Sum.inl i)) (y j)
  have hblock : Matrix.reindex e e ((quadraticMatrix q).submatrix id c) =
      Matrix.fromBlocks A B 0 D := by
    funext u v
    rcases u with i | p <;> rcases v with j | t
    · change quadraticMatrix q (e.symm (Sum.inl i)) (c (e.symm (Sum.inl j))) =
        weightedColumns q r i (x j)
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inl] using
        quadraticMatrix_request_top q r hqr (x j) i
    · change quadraticMatrix q (e.symm (Sum.inl i)) (c (e.symm (Sum.inr t))) =
        quadraticMatrix q (e.symm (Sum.inl i)) (y t)
      simp only [c, e, Equiv.apply_symm_apply, Sum.elim_inr]
    · change quadraticMatrix q (e.symm (Sum.inr p)) (c (e.symm (Sum.inl j))) = 0
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inl] using
        quadraticMatrix_request_bottom q r hqr (x j) p
    · change quadraticMatrix q (e.symm (Sum.inr p)) (c (e.symm (Sum.inr t))) =
        quadraticMatrix (fun m (i : Fin n) => q m i.succ) p (y t)
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inr] using
        quadraticMatrix_split_bottom q p (y t)
  exact ⟨c, (Matrix.det_reindex_self e ((quadraticMatrix q).submatrix id c)).symm.trans
    ((congrArg Matrix.det hblock).trans (Matrix.det_fromBlocks_zero₂₁ A B D))⟩

end KServerConj
end PaperFile039

section PaperFile040
namespace KServerConj

theorem minorVal_le_tuple {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) :
    minorVal G ≤ HahnSeries.addVal ℝ F (G.submatrix id x).det := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_le_tuple (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) G x

theorem exists_minorVal_minimizer {F I J : Type*}
    [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (a : ℝ)
    (ha : minorVal G = (a : WithTop ℝ)) :
    ∃ x : I ↪ J, HahnSeries.addVal ℝ F (G.submatrix id x).det = (a : WithTop ℝ) := by
  classical
  have hh : DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G =
      (a : WithTop ℝ) := (minorVal_eq_embeddingMinorVal G).symm.trans ha
  unfold DetValuationMilestone.embeddingMinorVal at hh
  obtain ⟨x, _, hx⟩ := (Finset.inf_le_iff (show (a : WithTop ℝ) < ⊤ by simp)).mp hh.le
  exact ⟨x, le_antisymm hx (hh.symm.trans_le (Finset.inf_le (Finset.mem_univ x)))⟩

end KServerConj
end PaperFile040

section PaperFile041
namespace KServerConj

theorem quadraticMatrix_old_bound_finite {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (a b : ℝ)
    (ha : minorVal (weightedColumns q r) = (a : WithTop ℝ))
    (hb : minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) = (b : WithTop ℝ)) :
    minorVal (quadraticMatrix q) ≤ ((a + b : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx⟩ := exists_minorVal_minimizer (weightedColumns q r) a ha
  obtain ⟨y, hy⟩ := exists_minorVal_minimizer
    (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) b hb
  obtain ⟨c, hc⟩ := quadraticMatrix_exists_old_minor q r hqr x y
  have hval : HahnSeries.addVal ℝ F ((quadraticMatrix q).submatrix id c).det =
      ((a + b : ℝ) : WithTop ℝ) := by
    simpa only [AddValuation.map_mul, hx, hy, WithTop.coe_add] using
      congrArg (HahnSeries.addVal ℝ F) hc
  exact (minorVal_le_tuple (quadraticMatrix q) c).trans_eq hval

theorem quadraticMatrix_old_bound {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) :
    minorVal (quadraticMatrix q) ≤
      minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) +
        minorVal (weightedColumns q r) := by
  by_cases hH : minorVal (weightedColumns q r) = ⊤
  · simp [hH]
  by_cases hT : minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) = ⊤
  · simp [hT]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hH
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hT
  simpa only [← ha, ← hb, WithTop.coe_add, add_comm] using
    quadraticMatrix_old_bound_finite q r hqr a b ha.symm hb.symm

end KServerConj
end PaperFile041

section PaperFile044
namespace KServerConj

theorem lemma_4_1 {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (q : M → Fin (m + 1) → K (m + 1) M) (r : M) (hr : q r = Pi.single 0 1) :
    Psi q ≤ minorVal (Qhat q) + minorVal (Hmat q r) := by
  change minorVal (quadraticMatrix q) ≤
    minorVal (quadraticMatrix (fun x (i : Fin m) => q x i.succ)) +
      minorVal (weightedColumns q r)
  exact quadraticMatrix_old_bound q r hr

end KServerConj
end PaperFile044

section PaperFile045
open scoped BigOperators

namespace KServerConj

noncomputable def finSuccThreeBlockEquiv (m : ℕ) : Fin (m + 1) ≃ PUnit ⊕ Fin m :=
  (finSuccEquiv m).trans ((Equiv.optionEquivSumPUnit (Fin m)).trans (Equiv.sumComm _ _))

noncomputable def quadraticThreeBlockEquiv (m : ℕ) :
    Sym2 (Fin (m + 1)) ≃ PUnit ⊕ (Fin m ⊕ Sym2 (Fin m)) :=
  (sym2FinSuccEquiv m).trans
    ((Equiv.sumCongr (finSuccThreeBlockEquiv m) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))

@[simp] theorem quadraticThreeBlockEquiv_symm_first (m : ℕ) (u : PUnit) :
    (quadraticThreeBlockEquiv m).symm (Sum.inl u) = s(0, 0) := by
  simp [quadraticThreeBlockEquiv, finSuccThreeBlockEquiv]

@[simp] theorem quadraticThreeBlockEquiv_symm_middle (m : ℕ) (i : Fin m) :
    (quadraticThreeBlockEquiv m).symm (Sum.inr (Sum.inl i)) = s(0, i.succ) := by
  simp [quadraticThreeBlockEquiv, finSuccThreeBlockEquiv]

@[simp] theorem quadraticThreeBlockEquiv_symm_last (m : ℕ) (p : Sym2 (Fin m)) :
    (quadraticThreeBlockEquiv m).symm (Sum.inr (Sum.inr p)) = p.map Fin.succ := by
  simp [quadraticThreeBlockEquiv]

noncomputable def quadraticNewReference {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) :
    Matrix (PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) (PUnit ⊕ (M ⊕ Sym2 M)) (HahnSeries ℝ F) :=
  Matrix.fromBlocks 1 0 0
    (Matrix.fromBlocks ((weightedColumns q r).submatrix Fin.succ id) 0 0
      (quadraticMatrix (fun y => Fin.tail (q y))))

noncomputable def quadraticNewCoefficients {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F) (x y : M) :
    PUnit ⊕ (M ⊕ Sym2 M) → HahnSeries ℝ F :=
  Sum.elim (fun _ => HahnSeries.single (-dist x y) (1 : F) * δ x * δ y)
    (Sum.elim (fun z =>
      (Pi.single y (HahnSeries.single (dist r y - dist x y) (1 : F) * δ x) :
        M → HahnSeries ℝ F) z +
      (Pi.single x (HahnSeries.single (dist r x - dist x y) (1 : F) * δ y) :
        M → HahnSeries ℝ F) z)
      (Pi.single s(x, y) 1 : Sym2 M → HahnSeries ℝ F))

theorem single_neg_mul_sub {F : Type*} [Field F] (a b : ℝ) :
    (HahnSeries.single (-a) (1 : F) : HahnSeries ℝ F) *
        HahnSeries.single (a - b) 1 = HahnSeries.single (-b) 1 := by
  simp [HahnSeries.single_mul_single, sub_eq_add_neg, ← add_assoc]

theorem weightedColumns_mul_shift {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin m → HahnSeries ℝ F) (r y : M)
    (i : Fin m) (b : ℝ) (a : HahnSeries ℝ F) :
    weightedColumns q r i y * (HahnSeries.single (dist r y - b) (1 : F) * a) =
      HahnSeries.single (-b) (1 : F) * a * q y i := by
  calc
    _ = (HahnSeries.single (-dist r y) (1 : F) *
        HahnSeries.single (dist r y - b) (1 : F)) * a * q y i := by
      dsimp only [weightedColumns]
      ring
    _ = _ := by rw [single_neg_mul_sub]

theorem quadraticNewColumn_expansion {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (x y : M) (i : PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) :
    quadraticMatrix (fun z => Fin.cons (δ z) (Fin.tail (q z)))
        ((quadraticThreeBlockEquiv m).symm i) s(x, y) =
      ∑ j, quadraticNewReference q r i j * quadraticNewCoefficients r δ x y j := by
  rcases i with u | (i | p)
  · simp [quadraticNewReference, quadraticNewCoefficients, mul_assoc]
  · simp [quadraticNewReference, quadraticNewCoefficients, symProd_apply, Fin.tail,
      Pi.single_apply, mul_ite, mul_add, Finset.sum_add_distrib, weightedColumns_mul_shift]
    simp only [(Fin.succ_ne_zero i).symm, if_false, mul_assoc, mul_comm, mul_left_comm]
  · induction p using Sym2.ind with
    | _ i j =>
      simp [quadraticNewReference, quadraticNewCoefficients, quadraticMatrix, symProd,
        Pi.single_apply, mul_ite, Fin.tail]

end KServerConj
end PaperFile045

section PaperFile046
namespace KServerConj

theorem addVal_single_one {F : Type*} [Field F] (a : ℝ) :
    HahnSeries.addVal ℝ F (HahnSeries.single a (1 : F)) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem quadraticNew_unit_nonneg {F : Type*} [Field F] {M : Type*} [PseudoMetricSpace M]
    (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F
      (HahnSeries.single (-dist x y) (1 : F) * δ x * δ y) := by
  rw [AddValuation.map_mul, AddValuation.map_mul, addVal_single_one, hδ, hδ,
    ← WithTop.coe_add, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr (by
    linarith [show dist x y ≤ dist r x + dist r y by
      simpa only [dist_comm x r] using dist_triangle x r y])

theorem quadraticNew_middle_nonneg {F : Type*} [Field F] {M : Type*} [PseudoMetricSpace M]
    (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F
      (HahnSeries.single (dist r y - dist x y) (1 : F) * δ x) := by
  rw [AddValuation.map_mul, addVal_single_one, hδ, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr (by
    linarith [show dist x y ≤ dist r x + dist r y by
      simpa only [dist_comm x r] using dist_triangle x r y])

theorem addVal_pi_single_nonneg {F J : Type*} [Field F] [DecidableEq J]
    (j z : J) (a : HahnSeries ℝ F) (ha : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F a) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F ((Pi.single j a : J → HahnSeries ℝ F) z) := by
  rw [Pi.single_apply]
  split_ifs
  · exact ha
  · simpa only [AddValuation.map_zero] using (le_top : (0 : WithTop ℝ) ≤ ⊤)

theorem quadraticNewCoefficients_nonneg {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M)
    (j : PUnit ⊕ (M ⊕ Sym2 M)) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (quadraticNewCoefficients r δ x y j) := by
  rcases j with u | (z | p)
  · exact quadraticNew_unit_nonneg r δ hδ x y
  · exact (le_min
      (addVal_pi_single_nonneg y z _ (quadraticNew_middle_nonneg r δ hδ x y))
      (addVal_pi_single_nonneg x z _ (by
        simpa only [dist_comm y x] using quadraticNew_middle_nonneg r δ hδ y x))).trans
      (AddValuation.map_add _ _ _)
  · exact addVal_pi_single_nonneg s(x, y) p 1 (by simp [AddValuation.map_one])

end KServerConj
end PaperFile046

section PaperFile047
namespace KServerConj

theorem det_row_equiv_tuple {R I I' J : Type*} [CommRing R]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (G : Matrix I J R) (e : I' ≃ I) (x : I → J) :
    ((G.submatrix e id).submatrix id (x ∘ e)).det = (G.submatrix id x).det := by
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
    Matrix.det_submatrix_equiv_self e (G.submatrix id x)

theorem minorVal_row_equiv_le {F I I' J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (e : I' ≃ I) :
    minorVal (G.submatrix e id) ≤ minorVal G := by
  rw [minorVal_eq_embeddingMinorVal G]
  exact Finset.le_inf (fun x _ => (minorVal_le_tuple (G.submatrix e id) (x ∘ e)).trans_eq
    (congrArg (HahnSeries.addVal ℝ F) (det_row_equiv_tuple G e x)))

theorem minorVal_row_equiv {F I I' J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (e : I' ≃ I) :
    minorVal (G.submatrix e id) = minorVal G := by
  refine le_antisymm (minorVal_row_equiv_le G e) ?_
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Function.comp_id,
    Matrix.submatrix_id_id] using minorVal_row_equiv_le (G.submatrix e id) e.symm

end KServerConj
end PaperFile047

section PaperFile048
open scoped BigOperators

namespace DetValuationMilestone

theorem det_mul_rectangular_expansion
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (G : Matrix I J R) (C : Matrix J I R) :
    (G * C).det =
      ∑ f : I → J, (∏ i, C (f i) i) * (G.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq,
    mul_comm, mul_assoc]

theorem valuation_prod_nonneg
    {R I : Type*} [CommMonoid R]
    (ν : R → WithTop ℝ) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (s : Finset I) (f : I → R)
    (hf : ∀ i ∈ s, (0 : WithTop ℝ) ≤ ν (f i)) :
    (0 : WithTop ℝ) ≤ ν (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hone]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, hmul]
    exact add_nonneg (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem valuation_det_mul_lower_bound
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J I R) (μ : WithTop ℝ)
    (hG : ∀ f : I → J, μ ≤ ν (G.submatrix id f).det)
    (hC : ∀ j i, (0 : WithTop ℝ) ≤ ν (C j i)) :
    μ ≤ ν (G * C).det := by
  rw [det_mul_rectangular_expansion]
  apply valuation_sum_lower_bound ν hzero hadd
  intro f _
  have hcoeff : (0 : WithTop ℝ) ≤ ν (∏ i, C (f i) i) :=
    valuation_prod_nonneg ν hone hmul Finset.univ (fun i => C (f i) i)
      (fun i _ => hC (f i) i)
  simpa only [hmul, zero_add] using add_le_add hcoeff (hG f)

theorem tupleMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    tupleMinorVal ν G ≤ tupleMinorVal ν (G * C) := by
  classical
  refine Finset.le_inf (fun e _ => ?_)
  change tupleMinorVal ν G ≤ ν (G * (C.submatrix id e)).det
  exact valuation_det_mul_lower_bound ν hzero hone hmul hadd G (C.submatrix id e)
    (tupleMinorVal ν G)
    (fun f => Finset.inf_le (f := fun x : I → J => ν (G.submatrix id x).det)
      (Finset.mem_univ f))
    (fun j i => hC j (e i))

theorem embeddingMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν (G * C) := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    tupleMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C hC

theorem embeddingMinorVal_mono_of_column_combinations
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (F : Matrix I K R)
    (hF : ∀ k, ∃ c : J → R,
      (∀ j, (0 : WithTop ℝ) ≤ ν (c j)) ∧ ∀ i, F i k = ∑ j, G i j * c j) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν F := by
  classical
  let C : Matrix J K R := Matrix.of fun j k => (hF k).choose j
  have hGC : G * C = F :=
    Matrix.ext (fun i k => by
      simpa only [Matrix.mul_apply, C, Matrix.of_apply] using ((hF k).choose_spec.2 i).symm)
  simpa only [hGC] using
    embeddingMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C
      (fun j k => (hF k).choose_spec.1 j)

end DetValuationMilestone
end PaperFile048

section PaperFile049
open scoped BigOperators

namespace KServerConj

theorem minorVal_mono_of_column_combinations {F I J K : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (G : Matrix I J (HahnSeries ℝ F)) (A : Matrix I K (HahnSeries ℝ F))
    (hA : ∀ k, ∃ c : J → HahnSeries ℝ F,
      (∀ j, (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (c j)) ∧
      ∀ i, A i k = ∑ j, G i j * c j) :
    minorVal G ≤ minorVal A := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_mono_of_column_combinations
      (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) (AddValuation.map_one _)
      (fun a b => AddValuation.map_mul _ a b) (fun a b => AddValuation.map_add _ a b)
      G A hA

end KServerConj
end PaperFile049

section PaperFile050
open scoped BigOperators

namespace KServerConj

theorem quadraticNewReference_le_updated_minorVal {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) :
    minorVal (quadraticNewReference q r) ≤
      minorVal (quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y)))) := by
  classical
  exact (minorVal_mono_of_column_combinations (quadraticNewReference q r)
    ((quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y)))).submatrix
      (quadraticThreeBlockEquiv m).symm id) (by
        intro c
        induction c using Sym2.ind with
        | _ x y =>
          exact ⟨quadraticNewCoefficients r δ x y,
            quadraticNewCoefficients_nonneg r δ hδ x y,
            quadraticNewColumn_expansion q r δ x y⟩)).trans_eq
      (minorVal_row_equiv (quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y))))
        (quadraticThreeBlockEquiv m).symm)

end KServerConj
end PaperFile050

section PaperFile051
open scoped BigOperators

namespace KServerConj

noncomputable def quadraticCoeffSingle {F : Type*} [Field F] {M : Type*}
    [DecidableEq M] (p : Sym2 M) (a : HahnSeries ℝ F) : Sym2 M → HahnSeries ℝ F :=
  Pi.single p a

noncomputable def quadraticOldTailCoefficients {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F)
    (x y : M) : Sym2 M → HahnSeries ℝ F :=
  quadraticCoeffSingle s(x, y) 1 -
    quadraticCoeffSingle s(r, y) ((δ r)⁻¹ * HahnSeries.single (dist r y - dist x y) 1 * δ x) -
    quadraticCoeffSingle s(r, x) ((δ r)⁻¹ * HahnSeries.single (dist r x - dist x y) 1 * δ y) +
    quadraticCoeffSingle s(r, r) ((δ r)⁻¹ * (δ r)⁻¹ * HahnSeries.single (-dist x y) 1 * δ x * δ y)

theorem quadraticOldTailCoefficients_comm {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F) (x y : M) :
    quadraticOldTailCoefficients r δ x y = quadraticOldTailCoefficients r δ y x := by
  funext p
  have hxy : (s(x, y) : Sym2 M) = s(y, x) := Sym2.eq_swap
  simp only [quadraticOldTailCoefficients, hxy, dist_comm x y, Pi.add_apply, Pi.sub_apply]
  congr 1
  · ring
  · congr 1
    ring

noncomputable def quadraticOldCoefficients {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F) :
    PUnit ⊕ (M ⊕ Sym2 M) → Sym2 M → HahnSeries ℝ F :=
  Sum.elim (fun _ => quadraticCoeffSingle s(r, r) ((δ r)⁻¹ * (δ r)⁻¹))
    (Sum.elim (fun x =>
      quadraticCoeffSingle s(r, x) (δ r)⁻¹ -
        quadraticCoeffSingle s(r, r) ((δ r)⁻¹ * (δ r)⁻¹ * HahnSeries.single (-dist r x) 1 * δ x))
      (Sym2.lift ⟨quadraticOldTailCoefficients r δ, quadraticOldTailCoefficients_comm r δ⟩))

theorem quadraticOldCoefficients_nonneg {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ))
    (j : PUnit ⊕ (M ⊕ Sym2 M)) (z : Sym2 M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (quadraticOldCoefficients r δ j z) := by
  have hinv : HahnSeries.addVal ℝ F (δ r)⁻¹ = 0 := by
    simp only [AddValuation.map_inv, hδ, dist_self, WithTop.coe_zero, neg_zero]
  have hradial (x : M) :
      HahnSeries.addVal ℝ F (HahnSeries.single (-dist r x) 1 * δ x) = 0 := by
    simp only [AddValuation.map_mul, addVal_single_one, hδ, ← WithTop.coe_add,
      neg_add_cancel, WithTop.coe_zero]
  have hunit (f : HahnSeries ℝ F) (hf : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F f) :
      (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F ((δ r)⁻¹ * f) := by
    simpa only [AddValuation.map_mul, hinv, zero_add] using hf
  have hadd {a b : HahnSeries ℝ F}
      (ha : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F a)
      (hb : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F b) :
      (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (a + b) :=
    (le_min ha hb).trans (AddValuation.map_add _ _ _)
  have hsub {a b : HahnSeries ℝ F}
      (ha : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F a)
      (hb : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F b) :
      (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (a - b) := by
    simpa only [sub_eq_add_neg, AddValuation.map_neg] using
      hadd ha (show (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (-b) by
        simpa only [AddValuation.map_neg] using hb)
  rcases j with u | (x | p)
  · simp only [quadraticOldCoefficients, Sum.elim_inl, quadraticCoeffSingle]
    exact addVal_pi_single_nonneg _ _ _ (hunit _ hinv.ge)
  · simp only [quadraticOldCoefficients, Sum.elim_inr, Sum.elim_inl,
      Pi.sub_apply, quadraticCoeffSingle]
    apply hsub
    · exact addVal_pi_single_nonneg _ _ _ hinv.ge
    · apply addVal_pi_single_nonneg
      simpa only [mul_assoc] using hunit _ (hunit _ (hradial x).ge)
  · induction p using Sym2.ind with
    | _ x y =>
      simp only [quadraticOldCoefficients, Sum.elim_inr, Sym2.lift_mk,
        quadraticOldTailCoefficients, Pi.add_apply, Pi.sub_apply, quadraticCoeffSingle]
      apply hadd
      · apply hsub
        · apply hsub
          · exact addVal_pi_single_nonneg _ _ _ (by simp only [AddValuation.map_one, le_refl])
          · apply addVal_pi_single_nonneg
            simpa only [mul_assoc] using hunit _ (quadraticNew_middle_nonneg r δ hδ x y)
        · apply addVal_pi_single_nonneg
          simpa only [mul_assoc, dist_comm y x] using
            hunit _ (quadraticNew_middle_nonneg r δ hδ y x)
      · apply addVal_pi_single_nonneg
        simpa only [mul_assoc] using hunit _ (hunit _ (quadraticNew_unit_nonneg r δ hδ x y))

theorem quadraticOldColumn_expansion {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hr : q r = Pi.single 0 1) (hc : δ r ≠ 0)
    (j : PUnit ⊕ (M ⊕ Sym2 M)) (i : PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) :
    quadraticNewReference q r i j =
      ∑ c, quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))
          ((quadraticThreeBlockEquiv m).symm i) c * quadraticOldCoefficients r δ j c := by
  classical
  rcases j with u | (x | p)
  · rcases i with v | (i | p)
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Pi.single_apply, mul_ite]
      field_simp [hc]
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite,
        (Fin.succ_ne_zero i).symm]
    · induction p using Sym2.ind with
      | _ a b =>
        simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
          quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite]
  · rcases i with v | (i | p)
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Pi.single_apply, mul_ite,
        mul_sub, Finset.sum_sub_distrib]
      field_simp [hc]
      ring
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite,
        mul_sub, Finset.sum_sub_distrib, weightedColumns, (Fin.succ_ne_zero i).symm]
      field_simp [hc]
    · induction p using Sym2.ind with
      | _ a b =>
        simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
          quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite,
          mul_sub, Finset.sum_sub_distrib]
  · induction p using Sym2.ind with
    | _ x y =>
      rcases i with v | (i | p)
      · simp [quadraticNewReference, quadraticOldCoefficients, quadraticOldTailCoefficients,
          quadraticCoeffSingle, quadraticMatrix, symProd, Pi.single_apply,
          mul_ite, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        field_simp [hc]
        simp only [mul_assoc, single_neg_mul_sub]
        ring
      · simp [quadraticNewReference, quadraticOldCoefficients, quadraticOldTailCoefficients,
          quadraticCoeffSingle, quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply,
          mul_ite, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          (Fin.succ_ne_zero i).symm]
        field_simp [hc]
        simp only [mul_assoc, single_neg_mul_sub]
        ring
      · induction p using Sym2.ind with
        | _ a b =>
          simp [quadraticNewReference, quadraticOldCoefficients, quadraticOldTailCoefficients,
            quadraticCoeffSingle, quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply,
            mul_ite, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem updated_minorVal_le_quadraticNewReference {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hr : q r = Pi.single 0 1)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) :
    minorVal (quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))) ≤
      minorVal (quadraticNewReference q r) := by
  classical
  have hc : δ r ≠ 0 := HahnSeries.orderTop_ne_top.mp
    (ne_of_eq_of_ne (hδ r) WithTop.coe_ne_top)
  calc
    _ = minorVal ((quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))).submatrix
        (quadraticThreeBlockEquiv m).symm id) :=
      (minorVal_row_equiv _ (quadraticThreeBlockEquiv m).symm).symm
    _ ≤ _ := minorVal_mono_of_column_combinations _ _ (by
      intro j
      exact ⟨quadraticOldCoefficients r δ j, quadraticOldCoefficients_nonneg r δ hδ j,
        fun i => quadraticOldColumn_expansion q r δ hr hc j i⟩)

theorem quadratic_new_potential_eq_reference {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hr : q r = Pi.single 0 1)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) :
    minorVal (quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))) =
      minorVal (quadraticNewReference q r) := by
  exact le_antisymm (updated_minorVal_le_quadraticNewReference q r δ hr hδ)
    (quadraticNewReference_le_updated_minorVal q r δ hδ)

end KServerConj
end PaperFile051

section PaperFile052
open scoped BigOperators

namespace DetValuationMilestone

theorem valuation_det_nonneg
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix I I R) (hA : ∀ i j, (0 : WithTop ℝ) ≤ ν (A i j)) :
    (0 : WithTop ℝ) ≤ ν A.det := by
  let S : Subring R :=
    { carrier := {x | (0 : WithTop ℝ) ≤ ν x}
      zero_mem' := (show (0 : WithTop ℝ) ≤ ν 0 from
        hzero.symm ▸ (le_top : (0 : WithTop ℝ) ≤ ⊤))
      one_mem' := (show (0 : WithTop ℝ) ≤ ν 1 from
        hone.symm ▸ (le_rfl : (0 : WithTop ℝ) ≤ 0))
      add_mem' := fun hx hy => (le_min hx hy).trans (hadd _ _)
      neg_mem' := fun {x} hx => (show (0 : WithTop ℝ) ≤ ν (-x) from (hneg x).symm ▸ hx)
      mul_mem' := fun {x y} hx hy => (show (0 : WithTop ℝ) ≤ ν (x * y) from
        (hmul x y).symm ▸ add_nonneg hx hy) }
  let B : Matrix I I S := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hmatrix : S.subtype.mapMatrix B = A := Matrix.ext (fun _ _ => rfl)
  have hmap : (↑(B.det) : R) = A.det :=
    (RingHom.map_det S.subtype B).trans (congrArg Matrix.det hmatrix)
  exact hmap ▸ (show (0 : WithTop ℝ) ≤ ν (↑(B.det) : R) from (B.det).property)

theorem zero_le_tupleMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ tupleMinorVal ν G := by
  classical
  exact Finset.le_inf (fun e _ => valuation_det_nonneg ν hzero hone hneg hmul hadd
    (G.submatrix id e) (fun i j => hG i (e j)))

theorem zero_le_embeddingMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd G hG

end DetValuationMilestone
end PaperFile052

section PaperFile053
open scoped BigOperators

namespace KServerAlgebra

theorem det_updateRow_eq_sum_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) (δ : ι → R) :
    (M.updateRow j δ).det =
      ∑ i, δ i * (M.updateCol i (Pi.single j 1)).det := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.adjugate_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem updateCol_column_family
    {ι M R : Type*} [DecidableEq ι]
    (q : M → ι → R) (X : ι → M) (i : ι) (r : M) :
    (Matrix.of fun a b => q (X b) a).updateCol i (q r) =
      Matrix.of (fun a b => q (Function.update X i r b) a) := by
  ext a b
  by_cases h : b = i <;> simp [Matrix.updateCol, Function.update, h]

theorem det_updateRow_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : M → ι → R) (X : ι → M) (r : M) (j : ι) (δ : ι → R)
    (hr : q r = Pi.single j 1) :
    ((Matrix.of fun a b => q (X b) a).updateRow j δ).det =
      ∑ i, δ i * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  simpa only [← hr, updateCol_column_family] using
    det_updateRow_eq_sum_updateCol (Matrix.of fun a b => q (X b) a) j δ

theorem rowReplace_column_matrix
    {n : ℕ} {M R : Type*}
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a) =
      (Matrix.of fun a b => q (X b) a).updateRow 0 (fun b => δ (X b)) := by
  ext a b
  cases a using Fin.cases <;> simp [Matrix.updateRow, Function.update, Fin.tail]

theorem det_rowReplace_column_family
    {n : ℕ} {M R : Type*} [CommRing R]
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M)
    (r : M) (hr : q r = Pi.single 0 1) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a).det =
      ∑ i, δ (X i) * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  rw [rowReplace_column_matrix]
  exact det_updateRow_column_family q X r 0 (fun i => δ (X i)) hr

theorem mulVec_column_matrix
    {ι M R : Type*} [Fintype ι] [CommRing R]
    (B : Matrix ι ι R) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a) =
      B * (Matrix.of fun a b => q (X b) a) := by
  rfl

theorem det_normalized_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (B : Matrix ι ι R) (hB : B.det = 1) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a).det =
      (Matrix.of fun a b => q (X b) a).det := by
  rw [mulVec_column_matrix, Matrix.det_mul, hB, one_mul]

end KServerAlgebra
end PaperFile053

section PaperFile054
open scoped BigOperators

namespace DetValuationMilestone

theorem exists_finite_inf_minimizer
    {X : Type*} [Fintype X] (f : X → WithTop ℝ) (μ : ℝ)
    (h : (Finset.univ.inf f) = (μ : WithTop ℝ)) :
    ∃ x, f x = (μ : WithTop ℝ) := by
  classical
  obtain ⟨i, _, hi⟩ := (Finset.inf_le_iff (show (μ : WithTop ℝ) < ⊤ by simp)).mp h.le
  exact ⟨i, le_antisymm hi (h.symm.trans_le (Finset.inf_le (Finset.mem_univ i)))⟩

theorem minimum_basis_coordinate_nonneg
    {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Field K]
    (ν : K → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (G : Matrix I J K) (x : I → J) (μ : ℝ)
    (hmin : tupleMinorVal ν G = (μ : WithTop ℝ))
    (hx : ν (G.submatrix id x).det = (μ : WithTop ℝ)) :
    ∀ i j, (0 : WithTop ℝ) ≤ ν (((G.submatrix id x)⁻¹ * G) i j) := by
  let A : Matrix I I K := G.submatrix id x
  have hval : ν A.det = (μ : WithTop ℝ) := hx
  have hAne : A.det ≠ 0 := fun hz =>
    (show (μ : WithTop ℝ) ≠ ⊤ by simp)
      ((hval.symm.trans (congrArg ν hz)).trans hzero)
  intro i j
  have hcr := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A (G.col j)
    (isUnit_iff_ne_zero.mpr hAne)) i
  have hcoord : A.det * ((A⁻¹ * G) i j) = (A.updateCol i (G.col j)).det := by
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Matrix.col_apply] using hcr
  have hmodified : (A.updateCol i (G.col j)).det =
      (G.submatrix id (Function.update x i j)).det := by
    exact congrArg Matrix.det (Matrix.ext (fun a b => by
      by_cases hb : b = i <;>
        simp [A, Matrix.updateCol, Matrix.submatrix, Function.update, hb]))
  have hfull : (μ : WithTop ℝ) ≤ ν (G.submatrix id (Function.update x i j)).det :=
    hmin.symm.trans_le (Finset.inf_le (f := fun y : I → J => ν (G.submatrix id y).det)
      (Finset.mem_univ (Function.update x i j)))
  rw [← hmodified, ← hcoord, hmul, hval] at hfull
  exact WithTop.le_of_add_le_add_left (x := (μ : WithTop ℝ)) (by simp)
    (by simpa only [add_zero] using hfull)

theorem valuation_det_inverse_of_finite
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (ν : R → WithTop ℝ) (hone : ν 1 = 0)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (A : Matrix I I R) (hA : IsUnit A.det) (μ : ℝ)
    (hval : ν A.det = (μ : WithTop ℝ)) :
    ν A⁻¹.det = ((-μ : ℝ) : WithTop ℝ) := by
  have hprod : ν A⁻¹.det + (μ : WithTop ℝ) = 0 := by
    simpa only [hmul, hval, hone] using congrArg ν (Matrix.det_nonsing_inv_mul_det A hA)
  exact (add_left_inj_of_ne_top (a := (μ : WithTop ℝ)) (by simp)).mp
    (by simpa only [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero] using hprod)

theorem submatrix_fromBlocks_sum_map
    {I₁ I₂ J₁ J₂ R : Type*} [Zero R]
    (G₁ : Matrix I₁ J₁ R) (G₂ : Matrix I₂ J₂ R)
    (x₁ : I₁ → J₁) (x₂ : I₂ → J₂) :
    (Matrix.fromBlocks G₁ 0 0 G₂).submatrix id (Sum.map x₁ x₂) =
      Matrix.fromBlocks (G₁.submatrix id x₁) 0 0 (G₂.submatrix id x₂) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem tupleMinorVal_fromBlocks_of_finite
    {I₁ I₂ J₁ J₂ R : Type*}
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂] [Field R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ a, ν (-a) = ν a)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (hadd : ∀ a b, min (ν a) (ν b) ≤ ν (a + b))
    (G₁ : Matrix I₁ J₁ R) (G₂ : Matrix I₂ J₂ R) (μ₁ μ₂ : ℝ)
    (hmin₁ : tupleMinorVal ν G₁ = (μ₁ : WithTop ℝ))
    (hmin₂ : tupleMinorVal ν G₂ = (μ₂ : WithTop ℝ)) :
    tupleMinorVal ν (Matrix.fromBlocks G₁ 0 0 G₂) = ((μ₁ + μ₂ : ℝ) : WithTop ℝ) := by
  obtain ⟨x₁, hx₁⟩ := exists_finite_inf_minimizer
    (fun x : I₁ → J₁ => ν (G₁.submatrix id x).det) μ₁ hmin₁
  obtain ⟨x₂, hx₂⟩ := exists_finite_inf_minimizer
    (fun x : I₂ → J₂ => ν (G₂.submatrix id x).det) μ₂ hmin₂
  let A₁ : Matrix I₁ I₁ R := G₁.submatrix id x₁
  let A₂ : Matrix I₂ I₂ R := G₂.submatrix id x₂
  let S : Matrix (I₁ ⊕ I₂) (J₁ ⊕ J₂) R := Matrix.fromBlocks G₁ 0 0 G₂
  let B : Matrix (I₁ ⊕ I₂) (I₁ ⊕ I₂) R := Matrix.fromBlocks A₁⁻¹ 0 0 A₂⁻¹
  let H : Matrix (I₁ ⊕ I₂) (J₁ ⊕ J₂) R :=
    Matrix.fromBlocks (A₁⁻¹ * G₁) 0 0 (A₂⁻¹ * G₂)
  have hproduct : B * S = H := by
    simp only [B, S, H, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero]
  have hn₁ := minimum_basis_coordinate_nonneg ν hzero hmul G₁ x₁ μ₁ hmin₁ hx₁
  have hn₂ := minimum_basis_coordinate_nonneg ν hzero hmul G₂ x₂ μ₂ hmin₂ hx₂
  have hH : ∀ (i : I₁ ⊕ I₂) (j : J₁ ⊕ J₂), (0 : WithTop ℝ) ≤ ν (H i j) := fun
    | Sum.inl i, Sum.inl j => hn₁ i j
    | Sum.inl i, Sum.inr j => by simp [H, hzero]
    | Sum.inr i, Sum.inl j => by simp [H, hzero]
    | Sum.inr i, Sum.inr j => hn₂ i j
  have hHmin := zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd H hH
  have hrow : tupleMinorVal ν H = ν B.det + tupleMinorVal ν S :=
    (congrArg (tupleMinorVal ν) hproduct).symm.trans (tupleMinorVal_mul ν hmul B S)
  have hunit₁ : IsUnit A₁.det := isUnit_iff_ne_zero.mpr (fun hz =>
    (show (μ₁ : WithTop ℝ) ≠ ⊤ by simp)
      ((hx₁.symm.trans (congrArg ν hz)).trans hzero))
  have hunit₂ : IsUnit A₂.det := isUnit_iff_ne_zero.mpr (fun hz =>
    (show (μ₂ : WithTop ℝ) ≠ ⊤ by simp)
      ((hx₂.symm.trans (congrArg ν hz)).trans hzero))
  have hinv₁ := valuation_det_inverse_of_finite ν hone hmul A₁ hunit₁ μ₁ hx₁
  have hinv₂ := valuation_det_inverse_of_finite ν hone hmul A₂ hunit₂ μ₂ hx₂
  have hBval : ν B.det = ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ) := by
    simp only [B, Matrix.det_fromBlocks_zero₂₁, hmul, hinv₁, hinv₂, ← WithTop.coe_add]
  have hscaled : (0 : WithTop ℝ) ≤ ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ) + tupleMinorVal ν S := by
    simpa only [hrow, hBval] using hHmin
  have hlower : ((μ₁ + μ₂ : ℝ) : WithTop ℝ) ≤ tupleMinorVal ν S :=
    WithTop.le_of_add_le_add_left (x := ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ)) (by simp)
      (by simpa only [← WithTop.coe_add,
        show (-μ₁ + -μ₂) + (μ₁ + μ₂) = 0 by linarith only,
        WithTop.coe_zero] using hscaled)
  have hselected : tupleMinorVal ν S ≤ ν (S.submatrix id (Sum.map x₁ x₂)).det :=
    Finset.inf_le (f := fun x : (I₁ ⊕ I₂) → (J₁ ⊕ J₂) => ν (S.submatrix id x).det)
      (Finset.mem_univ (Sum.map x₁ x₂))
  have hupper : tupleMinorVal ν S ≤ ((μ₁ + μ₂ : ℝ) : WithTop ℝ) := by
    simpa only [S, submatrix_fromBlocks_sum_map, Matrix.det_fromBlocks_zero₂₁,
      hmul, hx₁, hx₂, ← WithTop.coe_add] using hselected
  exact le_antisymm hupper hlower

end DetValuationMilestone
end PaperFile054

section PaperFile055
namespace KServerConj

theorem tupleMinorVal_one_punit {F : Type*} [Field F] :
    DetValuationMilestone.tupleMinorVal (HahnSeries.addVal ℝ F)
      (1 : Matrix PUnit PUnit (HahnSeries ℝ F)) = (0 : WithTop ℝ) := by
  classical
  simp [DetValuationMilestone.tupleMinorVal, Matrix.det_unique, Matrix.submatrix_apply,
    AddValuation.map_one]

theorem minorVal_one_punit {F : Type*} [Field F] :
    minorVal (1 : Matrix PUnit PUnit (HahnSeries ℝ F)) = (0 : WithTop ℝ) := by
  simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using
      (tupleMinorVal_one_punit (F := F))

set_option maxHeartbeats 1000000 in
theorem minorVal_fromBlocks_of_finite {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F))
    (a b : ℝ) (h₁ : minorVal G₁ = (a : WithTop ℝ)) (h₂ : minorVal G₂ = (b : WithTop ℝ)) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = ((a + b : ℝ) : WithTop ℝ) := by
  simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using
      DetValuationMilestone.tupleMinorVal_fromBlocks_of_finite (R := HahnSeries ℝ F)
        (HahnSeries.addVal ℝ F) (AddValuation.map_zero (HahnSeries.addVal ℝ F))
        (AddValuation.map_one (HahnSeries.addVal ℝ F))
        (fun x => AddValuation.map_neg (HahnSeries.addVal ℝ F) x)
        (fun x y => AddValuation.map_mul (HahnSeries.addVal ℝ F) x y)
        (fun x y => AddValuation.map_add (HahnSeries.addVal ℝ F) x y) G₁ G₂ a b
        (by
          simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
            (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using h₁)
        (by
          simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
            (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using h₂)

end KServerConj
end PaperFile055

section PaperFile056
open scoped BigOperators

namespace KServerConj

theorem exists_rightInverse_of_nonzero_minor
    {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J K) (x : I → J) (hx : (G.submatrix id x).det ≠ 0) :
    ∃ C : Matrix J I K, G * C = 1 := by
  classical
  refine ⟨(1 : Matrix J J K).submatrix id x * (G.submatrix id x)⁻¹, ?_⟩
  rw [← Matrix.mul_assoc]
  have hm : G * (1 : Matrix J J K).submatrix id x = G.submatrix id x := by
    simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] using
      Matrix.mul_submatrix_one (Equiv.refl J) x G
  exact (congrArg (fun B : Matrix I I K => B * (G.submatrix id x)⁻¹) hm).trans
    (Matrix.mul_nonsing_inv (G.submatrix id x) (isUnit_iff_ne_zero.mpr hx))

theorem exists_nonzero_minor_of_rightInverse
    {K I J : Type*} [CommRing K] [Nontrivial K]
    [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J K) (C : Matrix J I K) (hC : G * C = 1) :
    ∃ x : I → J, (G.submatrix id x).det ≠ 0 := by
  classical
  by_contra h
  simp only [not_exists, not_not] at h
  simpa only [DetValuationMilestone.det_mul_rectangular_expansion, h, mul_zero,
    Finset.sum_const_zero, Matrix.det_one, zero_ne_one] using congrArg Matrix.det hC

theorem rightInverse_fromBlocks_left
    {K I₁ I₂ J₁ J₂ : Type*} [CommRing K]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ K) (G₂ : Matrix I₂ J₂ K)
    (C : Matrix (J₁ ⊕ J₂) (I₁ ⊕ I₂) K)
    (hC : Matrix.fromBlocks G₁ 0 0 G₂ * C = 1) :
    G₁ * C.submatrix Sum.inl Sum.inl = 1 := by
  funext i j
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.submatrix,
    Matrix.one_apply] using
    congrFun (congrFun hC (Sum.inl i)) (Sum.inl j)

theorem rightInverse_fromBlocks_right
    {K I₁ I₂ J₁ J₂ : Type*} [CommRing K]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ K) (G₂ : Matrix I₂ J₂ K)
    (C : Matrix (J₁ ⊕ J₂) (I₁ ⊕ I₂) K)
    (hC : Matrix.fromBlocks G₁ 0 0 G₂ * C = 1) :
    G₂ * C.submatrix Sum.inr Sum.inr = 1 := by
  exact funext fun i => funext fun j => by
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.submatrix,
      Matrix.one_apply] using congrFun (congrFun hC (Sum.inr i)) (Sum.inr j)

theorem minorVal_ne_top_of_nonzero_minor
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J)
    (hx : (G.submatrix id x).det ≠ 0) : minorVal G ≠ ⊤ := by
  exact fun h => hx <| HahnSeries.orderTop_eq_top.mp <|
    top_le_iff.mp <| h ▸ minorVal_le_tuple G x

theorem minorVal_fromBlocks_eq_top_of_left
    {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F))
    (h₁ : minorVal G₁ = ⊤) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = ⊤ := by
  classical
  have hz : ∀ x : (I₁ ⊕ I₂) → (J₁ ⊕ J₂),
      ((Matrix.fromBlocks G₁ 0 0 G₂).submatrix id x).det = 0 :=
    fun x => Classical.byContradiction fun hx =>
      (exists_rightInverse_of_nonzero_minor (Matrix.fromBlocks G₁ 0 0 G₂) x hx).elim
        fun C hC =>
          (exists_nonzero_minor_of_rightInverse G₁ (C.submatrix Sum.inl Sum.inl)
            (rightInverse_fromBlocks_left G₁ G₂ C hC)).elim fun y hy =>
              (minorVal_ne_top_of_nonzero_minor G₁ y hy) h₁
  simp [minorVal_eq_embeddingMinorVal, DetValuationMilestone.embeddingMinorVal,
    hz, AddValuation.map_zero]

theorem minorVal_eq_top_of_all_tuple_minors_zero
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F))
    (hz : ∀ x : I → J, (G.submatrix id x).det = 0) : minorVal G = ⊤ := by
  classical
  simp [minorVal_eq_embeddingMinorVal, DetValuationMilestone.embeddingMinorVal,
    hz, AddValuation.map_zero]

theorem minorVal_fromBlocks_eq_top_of_right
    {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F))
    (h₂ : minorVal G₂ = ⊤) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = ⊤ := by
  exact minorVal_eq_top_of_all_tuple_minors_zero (Matrix.fromBlocks G₁ 0 0 G₂)
    fun x => Classical.byContradiction fun hx =>
      (exists_rightInverse_of_nonzero_minor (Matrix.fromBlocks G₁ 0 0 G₂) x hx).elim
        fun C hC =>
          (exists_nonzero_minor_of_rightInverse G₂ (C.submatrix Sum.inr Sum.inr)
            (rightInverse_fromBlocks_right G₁ G₂ C hC)).elim fun y hy =>
              (minorVal_ne_top_of_nonzero_minor G₂ y hy) h₂

theorem minorVal_fromBlocks
    {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F)) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = minorVal G₁ + minorVal G₂ := by
  exact (Classical.em (minorVal G₁ = ⊤)).elim
    (fun h₁ => by simpa [h₁] using minorVal_fromBlocks_eq_top_of_left G₁ G₂ h₁)
    (fun h₁ => (Classical.em (minorVal G₂ = ⊤)).elim
      (fun h₂ => by simpa [h₂] using minorVal_fromBlocks_eq_top_of_right G₁ G₂ h₂)
      (fun h₂ => (WithTop.ne_top_iff_exists.mp h₁).elim fun a ha =>
        (WithTop.ne_top_iff_exists.mp h₂).elim fun b hb => by
          simpa only [← ha, ← hb, WithTop.coe_add] using
            minorVal_fromBlocks_of_finite G₁ G₂ a b ha.symm hb.symm))

end KServerConj
end PaperFile056

section PaperFile060
namespace KServerConj

theorem lemma_4_2 {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (q : M → Fin (m + 1) → K (m + 1) M) (r : M)
    (hr : q r = Pi.single 0 1) (δ : M → K (m + 1) M)
    (hδ : ∀ x, nu (δ x) = ((dist r x : ℝ) : WithTop ℝ)) :
    Psi (rowReplace q δ) = minorVal (Qhat q) + minorVal (Hhat q r) := by
  change minorVal (quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))) =
    minorVal (quadraticMatrix (fun x => Fin.tail (q x))) +
      minorVal ((weightedColumns q r).submatrix Fin.succ id)
  rw [quadratic_new_potential_eq_reference.{_, _, 0} q r δ hr hδ]
  simp only [quadraticNewReference, minorVal_fromBlocks, minorVal_one_punit, zero_add, add_comm]

end KServerConj
end PaperFile060

section PaperFile061

end PaperFile061

section PaperFile062
set_option autoImplicit false

namespace KServerConj

theorem potential_pays_of_projected_values {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ} (hm : 1 ≤ m)
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M) (hr : q r = Pi.single 0 1)
    (δ : M → K (m + 1) M) (hδ : ∀ x, nu (δ x) = (dist r x : WithTop ℝ))
    (a b : ℝ) (ha : minorVal (Hmat q r) = (a : WithTop ℝ))
    (hb : minorVal (Hhat q r) = (b : WithTop ℝ)) :
    ((b - a : ℝ) : WithTop ℝ) + Psi q ≤ Psi (rowReplace q δ) := by
  have hold := lemma_4_1 hm q r hr
  have hnew := lemma_4_2 hm q r hr δ hδ
  rw [ha] at hold
  rw [hb] at hnew
  calc
    ((b - a : ℝ) : WithTop ℝ) + Psi q ≤
        ((b - a : ℝ) : WithTop ℝ) + (minorVal (Qhat q) + (a : WithTop ℝ)) :=
      add_le_add le_rfl hold
    _ = minorVal (Qhat q) + (((b - a : ℝ) : WithTop ℝ) + (a : WithTop ℝ)) :=
      add_left_comm _ _ _
    _ = minorVal (Qhat q) + (b : WithTop ℝ) := by rw [← WithTop.coe_add, sub_add_cancel]
    _ = Psi (rowReplace q δ) := hnew.symm

end KServerConj
end PaperFile062

section PaperFile065
namespace KServerConj

variable {k : ℕ} {M : Type*}

@[simp] theorem nu_zero : nu (0 : K k M) = ⊤ := by
  exact AddValuation.map_zero _

@[simp] theorem nu_one : nu (1 : K k M) = 0 := by
  exact AddValuation.map_one _

@[simp] theorem nu_eq_top_iff (f : K k M) : nu f = ⊤ ↔ f = 0 := by
  exact HahnSeries.orderTop_eq_top

theorem nu_mul (f g : K k M) : nu (f * g) = nu f + nu g := by
  exact AddValuation.map_mul _ f g

theorem nu_add (f g : K k M) : min (nu f) (nu g) ≤ nu (f + g) := by
  exact AddValuation.map_add _ f g

@[simp] theorem nu_zp (a : ℝ) : nu (zp a : K k M) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem varF_ne_zero (v : Var k M) : varF v ≠ 0 := by
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))).mpr
    (MvPolynomial.X_ne_zero v)

@[simp] theorem nu_coef (v : Var k M) : nu (coef v) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, coef, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) (varF_ne_zero v))

theorem nu_C {c : F k M} (hc : c ≠ 0) : nu (HahnSeries.C c : K k M) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) hc)

theorem coef_ne_zero (v : Var k M) : coef v ≠ 0 := by
  exact HahnSeries.single_ne_zero (varF_ne_zero v)

theorem zp_ne_zero (a : ℝ) : (zp a : K k M) ≠ 0 := by
  exact HahnSeries.single_ne_zero one_ne_zero

@[simp] theorem zp_zero : (zp 0 : K k M) = 1 := by
  exact HahnSeries.single_zero_one

theorem zp_add (a b : ℝ) : (zp (a + b) : K k M) = zp a * zp b := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F k M)) (s := 1)).symm

@[simp] theorem nu_neg (f : K k M) : nu (-f) = nu f := by
  exact AddValuation.map_neg _ _

@[simp] theorem nu_inv (f : K k M) : nu f⁻¹ = -(nu f) := by
  exact AddValuation.map_inv _

theorem nu_sum_ge {ι : Type*} [Fintype ι] (f : ι → K k M) (b : WithTop ℝ)
    (hf : ∀ i, b ≤ nu (f i)) : b ≤ nu (∑ i, f i) := by
  exact AddValuation.map_le_sum _ (fun i _ => hf i)

theorem nu_fresh_term (v : Var k M) (a : ℝ) (f : K k M) :
    nu (coef v * zp a * f) = (a : WithTop ℝ) + nu f := by
  simp only [nu_mul, nu_coef, nu_zp, zero_add]

theorem zp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (zp (∑ i ∈ s, a i) : K k M) = ∏ i ∈ s, zp (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, zp_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zp_add, ih]

end KServerConj
end PaperFile065

section PaperFile066
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem varF_algebraicIndependent : AlgebraicIndependent ℚ (@varF k M) := by
  exact (MvPolynomial.algebraicIndependent_X (Var k M) ℚ).map'
    (f := IsScalarTower.toAlgHom ℚ (MvPolynomial (Var k M) ℚ) (F k M))
    (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))

theorem varF_algebraicIndependent_over_complement (S : Set (Var k M)) :
    AlgebraicIndependent (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ))
      (fun i : S => varF (i : Var k M)) := by
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr
    ((AlgebraicIndependent.iff_adjoin_image_compl S).mp varF_algebraicIndependent).2

theorem fresh_vars_linearIndependent {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) :
    LinearIndependent
      (IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ))
      (fun i => varF (v i)) := by
  exact (varF_algebraicIndependent_over_complement (Set.range v)).linearIndependent.comp
    (fun i => ⟨v i, Set.mem_range_self i⟩)
    (fun _ _ h => hv (congrArg Subtype.val h))

theorem complement_closure_le_adjoin (S : Set (Var k M)) :
    Subfield.closure ((@varF k M) '' Sᶜ) ≤
      (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ)).toSubfield := by
  exact Subfield.closure_le.mpr (IntermediateField.subset_adjoin ℚ _)

theorem fresh_vars_sum_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (b : Fin N → F k M)
    (hb : ∀ i, b i ∈ Subfield.closure ((@varF k M) '' (Set.range v)ᶜ))
    (hne : ∃ i, b i ≠ 0) :
    ∑ i, varF (v i) * b i ≠ 0 := by
  intro hz
  let c : Fin N → IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ) :=
    fun i => ⟨b i, complement_closure_le_adjoin (Set.range v) (hb i)⟩
  have hsum : ∑ i, c i • varF (v i) = 0 := by
    simpa only [c, IntermediateField.smul_def, Subtype.coe_mk, smul_eq_mul, mul_comm] using hz
  have hczero := Fintype.linearIndependent_iff.mp (fresh_vars_linearIndependent v hv) c hsum
  exact hne.elim (fun i hi => hi (congrArg Subtype.val (hczero i)))

end KServerConj
end PaperFile066

section PaperFile067
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem coeff_fresh_term (v : Var k M) (a b : ℝ) (f : K k M) :
    (coef v * zp a * f).coeff b = varF v * f.coeff (b - a) := by
  simp only [mul_assoc, coef, HahnSeries.C_apply, zp, HahnSeries.coeff_single_mul,
    one_mul, sub_zero]

theorem fresh_sum_coeff_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) (b : ℝ)
    (hne : ∃ i, (f i).coeff (b - a i) ≠ 0) :
    (∑ i, coef (v i) * zp (a i) * f i).coeff b ≠ 0 := by
  simpa only [HahnSeries.coeff_sum, coeff_fresh_term] using
    fresh_vars_sum_ne_zero v hv (fun i => (f i).coeff (b - a i))
      (fun i => hf i (b - a i)) hne

theorem nu_fresh_sum_le_of_ne {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ)
    (j : Fin N) (hj : f j ≠ 0) :
    nu (∑ i, coef (v i) * zp (a i) * f i) ≤ (a j : WithTop ℝ) + nu (f j) := by
  have hcoeff := fresh_sum_coeff_ne_zero v hv f hf a (a j + (f j).order)
    ⟨j, by simpa only [add_sub_cancel_left] using (HahnSeries.coeff_order_eq_zero.not.mpr hj)⟩
  simpa only [nu, HahnSeries.addVal_apply_of_ne hj, ← WithTop.coe_add] using
    (HahnSeries.addVal_le_of_coeff_ne_zero hcoeff)

theorem fresh_coefficients_no_cancellation {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) :
    nu (∑ i, coef (v i) * zp (a i) * f i) =
      Finset.univ.inf (fun i => (a i : WithTop ℝ) + nu (f i)) := by
  apply le_antisymm
  · refine Finset.le_inf ?_
    intro j _
    exact (eq_or_ne (f j) 0).elim
      (fun hj => by simp only [hj, nu_zero, WithTop.add_top, le_top])
      (nu_fresh_sum_le_of_ne v hv f hf a j)
  · exact nu_sum_ge _ _ (fun i => by
      simpa only [nu_fresh_term] using
        (Finset.inf_le (f := fun i => (a i : WithTop ℝ) + nu (f i)) (Finset.mem_univ i)))

end KServerConj
end PaperFile067

section PaperFile068
namespace KServerConj

noncomputable def hahnCoeffMap {F E : Type*} [Field F] [Field E] (g : F →+* E) :
    HahnSeries ℝ F →+* HahnSeries ℝ E where
  toFun f := f.map g
  map_zero' := HahnSeries.map_zero g.toZeroHom
  map_one' := by
    simpa only [map_one] using (HahnSeries.map_C (Γ := ℝ) (1 : F) g)
  map_add' _ _ := HahnSeries.map_add g.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul g.toNonUnitalRingHom

@[simp] theorem hahnCoeffMap_coeff {F E : Type*} [Field F] [Field E]
    (g : F →+* E) (f : HahnSeries ℝ F) (a : ℝ) :
    (hahnCoeffMap g f).coeff a = g (f.coeff a) := rfl

noncomputable def restrictCoeffs {F : Type*} [Field F] (S : Subfield F) (f : HahnSeries ℝ F)
    (hf : ∀ a, f.coeff a ∈ S) : HahnSeries ℝ S where
  coeff a := ⟨f.coeff a, hf a⟩
  isPWO_support' := f.isPWO_support.mono fun _ ha hz => ha (Subtype.ext hz)

@[simp] theorem restrictCoeffs_map {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    hahnCoeffMap S.subtype (restrictCoeffs S f hf) = f := by
  exact HahnSeries.coeff_injective rfl

theorem coeff_inv_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    ∀ a, (f⁻¹).coeff a ∈ S := by
  have hmap : hahnCoeffMap S.subtype (restrictCoeffs S f hf)⁻¹ = f⁻¹ := by
    rw [map_inv₀, restrictCoeffs_map]
  exact fun a => (congrArg (fun g : HahnSeries ℝ F => g.coeff a) hmap) ▸
    (((restrictCoeffs S f hf)⁻¹).coeff a).property

end KServerConj
end PaperFile068

section PaperFile069
namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem freeOf_zero (S : Set (Var k M)) : FreeOf S (0 : K k M) := by
  exact fun _ => Subfield.zero_mem _

theorem freeOf_single (S : Set (Var k M)) (a : ℝ) (c : F k M)
    (hc : c ∈ Subfield.closure ((fun v => varF v) '' Sᶜ)) :
    FreeOf S (HahnSeries.single a c) := by
  intro b
  rw [HahnSeries.coeff_single]
  exact ite_mem.mpr ⟨fun _ => hc, fun _ => Subfield.zero_mem _⟩

theorem freeOf_zp (S : Set (Var k M)) (a : ℝ) : FreeOf S (zp a : K k M) := by
  exact freeOf_single S a 1 (Subfield.one_mem _)

theorem freeOf_one (S : Set (Var k M)) : FreeOf S (1 : K k M) := by
  exact freeOf_single S 0 1 (Subfield.one_mem _)

theorem freeOf_coef (S : Set (Var k M)) (v : Var k M) (hv : v ∉ S) :
    FreeOf S (coef v) := by
  exact freeOf_single S 0 (varF v) (Subfield.subset_closure ⟨v, hv, rfl⟩)

theorem freeOf_add {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f + g) := by
  simpa only [FreeOf, HahnSeries.coeff_add] using
    fun a => Subfield.add_mem _ (hf a) (hg a)

theorem freeOf_neg {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S (-f) := by
  simpa only [FreeOf, HahnSeries.coeff_neg] using
    fun a => Subfield.neg_mem _ (hf a)

theorem freeOf_mul {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f * g) := by
  intro a
  rw [HahnSeries.coeff_mul]
  exact Subfield.sum_mem _ fun ij _ => Subfield.mul_mem _ (hf ij.1) (hg ij.2)

theorem freeOf_inv {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S f⁻¹ := by
  exact coeff_inv_mem_subfield _ f hf

noncomputable def freeOfSubfield (S : Set (Var k M)) : Subfield (K k M) where
  carrier := FreeOf S
  zero_mem' := freeOf_zero S
  one_mem' := freeOf_one S
  add_mem' := freeOf_add
  mul_mem' := freeOf_mul
  neg_mem' := freeOf_neg
  inv_mem' := fun _ hf => freeOf_inv hf

theorem freeOf_div {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f / g) := by
  exact (freeOfSubfield S).div_mem hf hg

theorem freeOf_sum {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∑ i ∈ s, f i) := by
  exact (freeOfSubfield S).sum_mem hf

theorem freeOf_prod {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∏ i ∈ s, f i) := by
  exact (freeOfSubfield S).prod_mem hf

theorem freeOf_mono {S T : Set (Var k M)} {f : K k M} (hST : S ⊆ T)
    (hf : FreeOf T f) : FreeOf S f := by
  exact fun a => Subfield.closure_mono (Set.image_mono (Set.compl_subset_compl.mpr hST)) (hf a)

end KServerConj
end PaperFile069

section PaperFile070
namespace KServerConj

theorem colDet_eq_zero_of_not_injective {k : ℕ} {M : Type*}
    (q : M → Fin k → K k M) (x : Fin k → M) (hx : ¬ Function.Injective x) :
    colDet q x = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun a => congrArg (fun y => q y a) hij)

theorem update_injective_of_not_mem_range {ι M : Type*} [DecidableEq ι]
    (x : ι → M) (hx : Function.Injective x) (r : M) (hr : r ∉ Set.range x) (i : ι) :
    Function.Injective (Function.update x i r) := by
  intro a b hab
  by_cases ha : a = i
  · have hb : b = i := Classical.byContradiction fun hb => hr
      ⟨b, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab.symm⟩
    exact ha.trans hb.symm
  · have hb : b ≠ i := fun hb => hr
      ⟨a, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab⟩
    exact hx (by simpa only [Function.update_apply, ha, hb, if_false] using hab)

end KServerConj
end PaperFile070

section PaperFile071
open scoped BigOperators

namespace KServerConj

theorem colDet_rowReplace_eq_sum {n : ℕ} {M : Type*}
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (x : Fin (n + 1) → M) (r : M) (hr : q r = Pi.single 0 1) :
    colDet (rowReplace q δ) x =
      ∑ i, δ (x i) * colDet q (Function.update x i r) := by
  exact KServerAlgebra.det_rowReplace_column_family q δ x r hr

theorem fresh_rowReplace_valuation_eq_inf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ x : Fin (n + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) (colDet q x))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
        nu (colDet q (Function.update x i r))) := by
  have hv : Function.Injective (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) :=
    fun _ _ h => hx (congrArg (fun p : ℕ × M => p.2) (Sum.inr.inj h))
  have hsubset :
      Set.range (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) ⊆
        Set.range (fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) :=
    fun _ ⟨i, hi⟩ => ⟨x i, hi⟩
  exact (congrArg nu (colDet_rowReplace_eq_sum q
    (fun y => coef (Sum.inr (t, y)) * zp (dist r y)) x r hr)).trans
    (fresh_coefficients_no_cancellation
      (fun i => (Sum.inr (t, x i) : Var (n + 1) M)) hv
      (fun i => colDet q (Function.update x i r))
      (fun i => freeOf_mono hsubset (hfree (Function.update x i r)))
      (fun i => dist r (x i)))

theorem exists_injective_update_le {ι M : Type*} [DecidableEq ι] [PseudoMetricSpace M]
    (x : ι → M) (hx : Function.Injective x) (r : M)
    (w : (ι → M) → ℝ) (b : ℝ)
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b) (hmono : w x ≤ b) :
    ∃ i, Function.Injective (Function.update x i r) ∧
      w (Function.update x i r) + dist r (x i) ≤ b := by
  by_cases hrange : r ∈ Set.range x
  · exact hrange.elim (fun j hj =>
      let hu : Function.update x j r = x := Function.update_eq_self_iff.mpr hj.symm
      ⟨j, hu.symm ▸ hx, by simpa only [hu, hj, dist_self, add_zero] using hmono⟩)
  · exact hge.elim (fun i hi =>
      ⟨i, update_injective_of_not_mem_range x hx r hrange i, hi⟩)

theorem determinant_cost_inf_eq {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M)
    (w : (Fin (n + 1) → M) → ℝ) (b : ℝ)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (x : Fin (n + 1) → M) (hx : Function.Injective x)
    (hle : ∀ i, b ≤ w (Function.update x i r) + dist r (x i))
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b)
    (hmono : w x ≤ b) :
    Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
      nu (colDet q (Function.update x i r))) = (b : WithTop ℝ) := by
  apply le_antisymm
  · obtain ⟨i, hi, hcost⟩ := exists_injective_update_le x hx r w b hge hmono
    exact (Finset.inf_le
      (f := fun i => (dist r (x i) : WithTop ℝ) + nu (colDet q (Function.update x i r)))
      (Finset.mem_univ i)).trans (by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr hcost))
  · refine Finset.le_inf ?_
    intro i _
    exact (em (Function.Injective (Function.update x i r))).elim
      (fun hi => by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr (hle i)))
      (fun hi => by
        simp only [colDet_eq_zero_of_not_injective q _ hi, nu_zero, WithTop.add_top, le_top])

theorem request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : q r = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      (w' x : WithTop ℝ) := by
  exact (fresh_rowReplace_valuation_eq_inf q r t hr hfree x hx).trans
    (determinant_cost_inf_eq q r w (w' x) hrep x hx
      (hrec_le x hx) (hrec_ge x hx) (hmono x hx))

theorem rowReplace_det_freeOf {n : ℕ} {M : Type*} (S : Set (Var (n + 1) M))
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (r : M) (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hδ : ∀ y : M, FreeOf S (δ y)) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q δ) x) := by
  exact (colDet_rowReplace_eq_sum q δ x r hr).symm ▸
    freeOf_sum Finset.univ (fun i => δ (x i) * colDet q (Function.update x i r))
      (fun i _ => freeOf_mul (hδ (x i)) (hfree (Function.update x i r)))

theorem fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M)) (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact rowReplace_det_freeOf S q _ r hr hfree
    (fun y => freeOf_mul (freeOf_coef S (Sum.inr (t, y)) (hS y)) (freeOf_zp S (dist r y))) x

theorem colDet_normalize_eq {k : ℕ} {M : Type*}
    (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1)
    (q : M → Fin k → K k M) (x : Fin k → M) :
    colDet (fun y => B.mulVec (q y)) x = colDet q x := by
  exact KServerAlgebra.det_normalized_column_family B hB q x

theorem normalized_request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : B.mulVec (q r) = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) = (w' x : WithTop ℝ) := by
  exact request_representation_step (fun y => B.mulVec (q y)) r t w w' hr
    (fun y hy => (congrArg nu (colDet_normalize_eq B hB q y)).trans (hrep y hy))
    (fun y => (colDet_normalize_eq B hB q y).symm ▸ hfree y)
    hrec_le hrec_ge hmono x hx

theorem normalized_fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : B.mulVec (q r) = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact fresh_rowReplace_det_freeOf S (fun y => B.mulVec (q y)) r t hr
    (fun y => (colDet_normalize_eq B hB q y).symm ▸ hfree y) hS x

end KServerConj
end PaperFile071

section PaperFile072
open scoped BigOperators

namespace KServerAlgebra

theorem exists_nonsingular_matrix_with_first_column
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      A.det ≠ 0 ∧ (fun r => A r 0) = v := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  refine ⟨((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K).updateCol j v).submatrix
    id (Equiv.swap 0 j), ?_, ?_⟩
  · rw [Matrix.det_permute']
    apply mul_ne_zero
    · exact ((Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) j)).isUnit.map
        (Int.castRingHom K)).ne_zero
    · simpa [← Matrix.cramer_apply] using hj
  · exact funext (fun r => by simp [Matrix.submatrix])

theorem exists_nonsingular_normalizer
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ T : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      T.det ≠ 0 ∧ T.mulVec v = Pi.single 0 1 := by
  obtain ⟨A, hA, hcol⟩ := exists_nonsingular_matrix_with_first_column v hv
  refine ⟨A⁻¹, (A.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr hA)).ne_zero, ?_⟩
  have hvec : A.mulVec (Pi.single 0 1) = v := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply'] using hcol
  rw [← hvec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]

theorem exists_det_one_normalizer
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 2) → K) (hv : v ≠ 0) :
    ∃ B : Matrix (Fin (n + 2)) (Fin (n + 2)) K,
      B.det = 1 ∧ B.mulVec v = Pi.single 0 1 := by
  obtain ⟨T, hT, hTv⟩ := exists_nonsingular_normalizer v hv
  refine ⟨T.updateRow 1 (T.det⁻¹ • T 1), ?_, ?_⟩
  · rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, inv_mul_cancel₀ hT]
  · have hrow : dotProduct (T 1) v = 0 := by
      simpa [Matrix.mulVec] using congrFun hTv 1
    simp [Matrix.updateRow_mulVec, smul_dotProduct, hrow, hTv]

end KServerAlgebra
end PaperFile072

section PaperFile073
set_option autoImplicit false

namespace KServerConj

noncomputable def hahnCoeffRingMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : HahnSeries ℝ R →+* HahnSeries ℝ S where
  toFun a := a.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] theorem hahnCoeffRingMap_coeff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : HahnSeries ℝ R) (t : ℝ) :
    (hahnCoeffRingMap f a).coeff t = f (a.coeff t) := rfl

@[simp] theorem hahnCoeffRingMap_single {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : ℝ) (r : R) :
    hahnCoeffRingMap f (HahnSeries.single a r) = HahnSeries.single a (f r) := by
  exact HahnSeries.map_single f.toZeroHom

end KServerConj
end PaperFile073

section PaperFile074
namespace KServerConj

theorem nu_det_C {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (F k M)) (hA : A.det ≠ 0) :
    nu (((HahnSeries.C : F k M →+* K k M).mapMatrix A).det) = 0 := by
  exact (congrArg nu ((HahnSeries.C : F k M →+* K k M).map_det A).symm).trans (nu_C hA)

end KServerConj
end PaperFile074

section PaperFile075
namespace KServerConj

theorem freeOf_det {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (Var k M)} (A : Matrix ι ι (K k M)) (hA : ∀ i j, FreeOf S (A i j)) :
    FreeOf S A.det := by
  let B : Matrix ι ι (freeOfSubfield S) := fun i j => ⟨A i j, hA i j⟩
  exact ((freeOfSubfield S).subtype.map_det B) ▸ B.det.property

end KServerConj
end PaperFile075

section PaperFile076
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem gamma_det_ne_zero (x : Fin k → M) (hx : Function.Injective x) :
    (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j))).det ≠ 0 := by
  let ρ : Fin k × Fin k → Var k M := fun ij => Sum.inl (ij.1, x ij.2)
  have hρ : Function.Injective ρ := fun a b h =>
    let h' : (a.1, x a.2) = (b.1, x b.2) := Sum.inl.inj h
    Prod.ext (congrArg (fun z : Fin k × M => z.1) h')
      (hx (congrArg (fun z : Fin k × M => z.2) h'))
  have hAI := (@varF_algebraicIndependent k M).comp ρ hρ
  have hne := (map_ne_zero_iff (MvPolynomial.aeval ((@varF k M) ∘ ρ))
    (algebraicIndependent_iff_injective_aeval.mp hAI)).mpr
      (Matrix.det_mvPolynomialX_ne_zero (m := Fin k) (R := ℚ))
  simpa [AlgHom.map_det, Matrix.mvPolynomialX, Matrix.map, ρ] using hne

theorem nu_gamma_det (x : Fin k → M) (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det) = 0 := by
  exact nu_det_C (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j)))
    (gamma_det_ne_zero x hx)

theorem weighted_gamma_det_valuation (w : M → ℝ) (x : Fin k → M)
    (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det) =
      ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  have hfactor :
      (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det =
        (∏ j, (zp (w (x j)) : K k M)) *
          (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det := by
    simpa only [Matrix.of_apply, mul_comm] using
      Matrix.det_mul_row (fun j => (zp (w (x j)) : K k M))
        (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)))
  rw [hfactor, ← zp_sum Finset.univ (fun j => w (x j)), nu_mul, nu_zp,
    nu_gamma_det x hx, add_zero]

theorem initCols_colDet_valuation_of_uniform_dist [PseudoMetricSpace M]
    (s : Fin k → M) (w : M → ℝ) (hd : ∀ i y, dist (s i) y = w y)
    (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols s) x) = ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  simpa only [colDet, initCols, hd] using weighted_gamma_det_valuation w x hx

theorem initCols_coalesced_valuation [PseudoMetricSpace M]
    (p : M) (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols (fun _ : Fin k => p)) x) =
      ((∑ j, dist p (x j) : ℝ) : WithTop ℝ) := by
  exact initCols_colDet_valuation_of_uniform_dist (fun _ => p) (dist p) (fun _ _ => rfl) x hx

theorem initCols_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (y : M) (i : Fin k) : FreeOf S (initCols s y i) := by
  exact freeOf_mul (freeOf_coef S (Sum.inl (i, y)) (hS i y))
    (freeOf_zp S (dist (s i) y))

theorem colDet_freeOf (S : Set (Var k M)) (q : M → Fin k → K k M)
    (x : Fin k → M) (hq : ∀ i j, FreeOf S (q (x j) i)) : FreeOf S (colDet q x) := by
  exact freeOf_det (Matrix.of fun i j => q (x j) i) hq

theorem initCols_colDet_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (x : Fin k → M) : FreeOf S (colDet (initCols s) x) := by
  exact colDet_freeOf S (initCols s) x (fun i j => initCols_freeOf S hS s (x j) i)

end KServerConj
end PaperFile076

section PaperFile077
open scoped BigOperators

namespace KServerConj

theorem det_eq_one_of_weight {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A : Matrix ι ι R) (weight : ι → ℕ)
    (h : ∀ i j, weight j ≤ weight i → A i j = (1 : Matrix ι ι R) i j) :
    A.det = 1 := by
  have ht : A.BlockTriangular weight := by
    intro i j hij
    rw [h i j hij.le]
    exact Matrix.one_apply_ne (fun he => (ne_of_lt hij) (congrArg weight he).symm)
  have hb (n : ℕ) : A.toSquareBlock weight n = 1 := by
    ext i j
    change A i.val j.val = (1 : Matrix { a // weight a = n } { a // weight a = n } R) i j
    simpa [Matrix.one_apply, Subtype.ext_iff] using
      h i.val j.val (le_of_eq (j.property.trans i.property.symm))
  simpa [hb] using ht.det

def symCount {ι : Type*} [DecidableEq ι] (a : ι) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun i j => (if i = a then 1 else 0) + (if j = a then 1 else 0), by
    intro i j
    exact Nat.add_comm _ _⟩

@[simp] theorem symCount_mk {ι : Type*} [DecidableEq ι] (a i j : ι) :
    symCount a s(i, j) = (if i = a then 1 else 0) + (if j = a then 1 else 0) := rfl

theorem transvection_col {R : Type*} [CommRing R] {k : ℕ}
    (i j l : Fin k) (c : R) :
    (Matrix.transvection i j c).col l =
      Pi.single l 1 + if l = j then c • Pi.single i 1 else 0 := by
  ext r
  by_cases hl : l = j <;> by_cases hr : r = i <;>
    simp_all [Matrix.transvection, Matrix.col, Matrix.single, Matrix.one_apply,
      Pi.single_apply, eq_comm]

theorem sym2Mat_transvection_weight {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) (p q : Sym2 (Fin k))
    (hw : symCount j q ≤ symCount j p) :
    sym2Mat (Matrix.transvection i j c) p q = (1 : Matrix _ _ R) p q := by
  have hz (z : Sym2 (Fin k)) (hzp : symCount j z < symCount j p) :
      (Pi.single z (1 : R) : Sym2 (Fin k) → R) p = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Sym2 (Fin k) => R)
      (fun he => hzp.ne (congrArg (symCount j) he).symm) (1 : R)
  induction q using Sym2.ind with
  | _ x y =>
    change symProd ((Matrix.transvection i j c).col x)
      ((Matrix.transvection i j c).col y) p = _
    by_cases hx : x = j <;> by_cases hy : y = j
    · have h0 := hz s(i, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      have h1 := hz s(i, j) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, symProd_add_left,
        symProd_add_right, symProd_smul_left, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        show s(j, i) = s(i, j) from Sym2.eq_swap, h0, h1, mul_zero, add_zero]
      simp [hx, hy, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(i, y) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_left, symProd_smul_left, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hx, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(x, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_right, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hy, Matrix.one_apply, Pi.single_apply]
    · simp [transvection_col, hx, hy, symProd_single_single, Matrix.one_apply, Pi.single_apply]

theorem det_sym2Mat_transvection {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) :
    (sym2Mat (Matrix.transvection i j c)).det = 1 := by
  exact det_eq_one_of_weight _ (symCount j) (sym2Mat_transvection_weight i j c hij)

theorem sym2_mk_left_injective {ι : Type*} (i : ι) :
    Function.Injective (fun j : ι => s(i, j)) :=
  fun _ _ h => (Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1)

theorem symCount_eq_zero_of_not_mem_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : Sym2 ι)
    (hp : p ∉ Finset.univ.image (fun j : ι => s(i, j))) : symCount i p = 0 := by
  induction p using Sym2.ind with
  | _ x y =>
    have hx : x ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, congrArg (fun a => s(a, y)) h.symm⟩)
    have hy : y ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, (Sym2.eq_swap : s(i, x) = s(x, i)).trans
        (congrArg (fun a => s(x, a)) h.symm)⟩)
    simp [symCount_mk, hx, hy]

theorem sum_symCount {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∑ p : Sym2 ι, symCount i p = Fintype.card ι + 1 := by
  have hs : (∑ p ∈ Finset.univ.image (fun j : ι => s(i, j)), symCount i p) =
      ∑ p : Sym2 ι, symCount i p :=
    Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => symCount_eq_zero_of_not_mem_image i p hp)
  rw [← hs, Finset.sum_image (sym2_mk_left_injective i).injOn]
  simp [symCount_mk, Finset.sum_add_distrib]

def symPairMul {ι R : Type*} [CommMonoid R] (d : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => d i * d j, fun i j => mul_comm (d i) (d j)⟩

@[simp] theorem symPairMul_mk {ι R : Type*} [CommMonoid R]
    (d : ι → R) (i j : ι) : symPairMul d s(i, j) = d i * d j := rfl

theorem symPairMul_eq_prod {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) (p : Sym2 ι) :
    symPairMul d p = ∏ i : ι, d i ^ symCount i p := by
  induction p using Sym2.ind with
  | _ x y =>
    simp only [symPairMul_mk, symCount_mk, pow_add, Finset.prod_mul_distrib]
    simp only [Finset.prod_pow_boole, Finset.mem_univ, ite_true]

theorem prod_symPairMul {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) :
    (∏ p : Sym2 ι, symPairMul d p) = (∏ i : ι, d i) ^ (Fintype.card ι + 1) := by
  simp_rw [symPairMul_eq_prod]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, sum_symCount]
  exact Finset.prod_pow _ _ _

theorem sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    sym2Mat (Matrix.diagonal d) = Matrix.diagonal (symPairMul d) := by
  have hs (i : Fin k) (a : R) :
      (Pi.single i a : Fin k → R) = a • Pi.single i 1 := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i a (1 : R)
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [Matrix.mulVec_single_one, sym2Mat_col, Matrix.col_diagonal, symPairMul_mk]
    rw [hs i (d i), hs j (d j), symProd_smul_left, symProd_smul_right,
      symProd_single_single, smul_smul]
    simp only [← Pi.single_smul', smul_eq_mul, mul_one]

theorem det_sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    (sym2Mat (Matrix.diagonal d)).det = (Matrix.diagonal d).det ^ (k + 1) := by
  simp only [sym2Mat_diagonal, Matrix.det_diagonal, prod_symPairMul, Fintype.card_fin]

theorem det_sym2Mat {K : Type*} [Field K] {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  apply Matrix.diagonal_transvection_induction
    (fun M : Matrix (Fin k) (Fin k) K => (sym2Mat M).det = M.det ^ (k + 1)) A
  · exact fun d _ => det_sym2Mat_diagonal d
  · intro t
    simpa [Matrix.TransvectionStruct.toMatrix, t.hij] using
      det_sym2Mat_transvection t.i t.j t.c t.hij
  · intro M N hM hN
    rw [sym2Mat_mul, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]

end KServerConj
end PaperFile077

section PaperFile078
open scoped BigOperators

namespace KServerConj

theorem single_add_one {F : Type*} [Field F] (a b : ℝ) :
    (HahnSeries.single (a + b) (1 : F) : HahnSeries ℝ F) =
      HahnSeries.single a (1 : F) * HahnSeries.single b (1 : F) := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F)) (s := 1)).symm

theorem single_sum_one {F ι : Type*} [Field F] (s : Finset ι) (a : ι → ℝ) :
    (HahnSeries.single (∑ i ∈ s, a i) (1 : F) : HahnSeries ℝ F) =
      ∏ i ∈ s, HahnSeries.single (a i) (1 : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, HahnSeries.single_zero_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, single_add_one, ih]

theorem quadraticMatrix_selected_det {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    ((quadraticMatrix q).submatrix id (Sym2.map x)).det =
      HahnSeries.single (∑ c, negPairDist x c) (1 : F) *
        (Matrix.of (fun i j => q (x j) i)).det ^ (k + 1) := by
  rw [quadraticMatrix_submatrix]
  rw [Matrix.det_mul_row (fun c => HahnSeries.single (negPairDist x c) (1 : F))
    (sym2Mat (Matrix.of (fun i j => q (x j) i)))]
  rw [det_sym2Mat, ← single_sum_one]

theorem quadraticMatrix_selected_valuation {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    HahnSeries.addVal ℝ F ((quadraticMatrix q).submatrix id (Sym2.map x)).det =
      ((∑ c, negPairDist x c) + ((k : ℝ) + 1) * δ : ℝ) := by
  rw [quadraticMatrix_selected_det, AddValuation.map_mul, AddValuation.map_pow, hD]
  rw [show HahnSeries.addVal ℝ F
      (HahnSeries.single (∑ c, negPairDist x c) (1 : F)) =
      (((∑ c, negPairDist x c) : ℝ) : WithTop ℝ) from HahnSeries.orderTop_single one_ne_zero]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

theorem negPairDist_nonpos {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) (c : Sym2 (Fin k)) : negPairDist x c ≤ 0 := by
  induction c using Sym2.ind with
  | _ i j => exact neg_nonpos.mpr dist_nonneg

theorem minorVal_quadratic_le {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    minorVal (quadraticMatrix q) ≤ ((((k : ℝ) + 1) * δ : ℝ) : WithTop ℝ) := by
  exact (minorVal_le_tuple (quadraticMatrix q) (Sym2.map x)).trans
    ((quadraticMatrix_selected_valuation q x δ hD).le.trans
      (WithTop.coe_le_coe.mpr (add_le_of_nonpos_left
        (Finset.sum_nonpos fun c _ => negPairDist_nonpos x c))))

end KServerConj
end PaperFile078

section PaperFile079
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem hahn_valuation_prod {F I : Type*} [Field F]
    (s : Finset I) (f : I → HahnSeries ℝ F) :
    HahnSeries.addVal ℝ F (∏ i ∈ s, f i) =
      ∑ i ∈ s, HahnSeries.addVal ℝ F (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, AddValuation.map_mul, ih]

theorem hahn_valuation_sign_smul {F : Type*} [Field F]
    (ε : ℤˣ) (a : HahnSeries ℝ F) :
    HahnSeries.addVal ℝ F (ε • a) = HahnSeries.addVal ℝ F a := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [Units.smul_def]

theorem weighted_det_valuation_lower {F I : Type*} [Field F]
    [Fintype I] [DecidableEq I] (A : Matrix I I (HahnSeries ℝ F))
    (a : I → I → ℝ)
    (hA : ∀ i j, HahnSeries.addVal ℝ F (A i j) = (a i j : WithTop ℝ))
    (b : ℝ) (hb : ∀ σ : Equiv.Perm I, b ≤ ∑ i, a (σ i) i) :
    (b : WithTop ℝ) ≤ HahnSeries.addVal ℝ F A.det := by
  rw [Matrix.det_apply]
  apply AddValuation.map_le_sum (HahnSeries.addVal ℝ F)
  intro σ _
  rw [hahn_valuation_sign_smul, hahn_valuation_prod]
  simpa only [hA, ← WithTop.coe_sum] using (WithTop.coe_le_coe.mpr (hb σ))

end KServerConj
end PaperFile079

section PaperFile080
open scoped BigOperators

namespace KServerConj

noncomputable def imageEquiv {M : Type*} [DecidableEq M] {k : ℕ}
    (x : Fin k → M) (hx : Function.Injective x) :
    Fin k ≃ {y : M // y ∈ Finset.univ.image x} := by
  refine Equiv.ofBijective (fun i => ⟨x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) ?_
  constructor
  · exact fun _ _ h => hx (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, rfl⟩

@[simp] theorem imageEquiv_apply_val {M : Type*} [DecidableEq M] {k : ℕ}
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) :
    (imageEquiv x hx i : M) = x i := rfl

theorem imageEquiv_symm_val {M : Type*} [DecidableEq M] {k : ℕ}
    (x : Fin k → M) (hx : Function.Injective x) (y : {y : M // y ∈ Finset.univ.image x}) :
    x ((imageEquiv x hx).symm y) = (y : M) := by
  exact congrArg Subtype.val ((imageEquiv x hx).apply_symm_apply y)

noncomputable def rowPermOfMatching {M : Type*} [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (e : (Finset.univ.image x : Finset M) ≃ (Finset.univ.image s : Finset M)) :
    Equiv.Perm (Fin k) :=
  ((imageEquiv x hx).trans e).trans (imageEquiv s hs).symm

theorem matching_cost_rowPerm {M : Type*} [PseudoMetricSpace M] [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (e : (Finset.univ.image x : Finset M) ≃ (Finset.univ.image s : Finset M)) :
    (∑ y : (Finset.univ.image x : Finset M), dist (y : M) (e y : M)) =
      ∑ j : Fin k, dist (s (rowPermOfMatching s x hs hx e j)) (x j) := by
  simpa only [rowPermOfMatching, Equiv.trans_apply, imageEquiv_apply_val,
    imageEquiv_symm_val, dist_comm] using
      ((imageEquiv x hx).sum_comp
        (fun y : (Finset.univ.image x : Finset M) => dist (y : M) (e y : M))).symm

noncomputable def matchingOfRowPerm {M : Type*} [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin k)) :
    (Finset.univ.image x : Finset M) ≃ (Finset.univ.image s : Finset M) :=
  (((imageEquiv x hx).symm.trans σ).trans (imageEquiv s hs))

theorem matching_cost_perm {M : Type*} [PseudoMetricSpace M] [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin k)) :
    (∑ y : (Finset.univ.image x : Finset M),
      dist (y : M) (matchingOfRowPerm s x hs hx σ y : M)) =
      ∑ j : Fin k, dist (s (σ j)) (x j) := by
  simpa only [rowPermOfMatching, matchingOfRowPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply] using
      matching_cost_rowPerm s x hs hx (matchingOfRowPerm s x hs hx σ)

theorem confDist_images_min_rowPerm {M : Type*} [PseudoMetricSpace M] [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x) :
    ∃ σ : Equiv.Perm (Fin k),
      confDist (Finset.univ.image s) (Finset.univ.image x) =
        (∑ j : Fin k, dist (s (σ j)) (x j)) ∧
      ∀ τ : Equiv.Perm (Fin k),
        (∑ j : Fin k, dist (s (σ j)) (x j)) ≤ ∑ j : Fin k, dist (s (τ j)) (x j) := by
  have hcard : (Finset.univ.image x).card = (Finset.univ.image s).card := by
    simpa using Fintype.card_congr ((imageEquiv x hx).symm.trans (imageEquiv s hs))
  obtain ⟨e, he⟩ := confDist_minimizer (Finset.univ.image x) (Finset.univ.image s) hcard
  let σ := rowPermOfMatching s x hs hx e
  have hcost : (∑ j : Fin k, dist (s (σ j)) (x j)) =
      confDist (Finset.univ.image x) (Finset.univ.image s) :=
    (matching_cost_rowPerm s x hs hx e).symm.trans he
  refine ⟨σ, ?_, ?_⟩
  · exact (confDist_symm _ _ hcard.symm).trans hcost.symm
  · intro τ
    rw [hcost]
    exact (confDist_le_matching _ _ (matchingOfRowPerm s x hs hx τ)).trans_eq
      (matching_cost_perm s x hs hx τ)

end KServerConj
end PaperFile080

section PaperFile081
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

noncomputable def permutationSelector {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V) (σ : Equiv.Perm (Fin k)) (w : V) : ℚ := by
  classical
  exact if w ∈ Finset.univ.image (fun j => v (σ j) j) then 1 else 0

theorem permutationSelector_apply {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (σ : Equiv.Perm (Fin k)) (i j : Fin k) :
    permutationSelector v σ (v i j) = if i = σ j then 1 else 0 := by
  classical
  have hmem : v i j ∈ Finset.univ.image (fun a => v (σ a) a) ↔ i = σ j := by
    constructor
    · intro h
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
      have hp := @hv (σ a, a) (i, j) ha
      have hj : a = j := congrArg Prod.snd hp
      simpa only [hj] using (congrArg Prod.fst hp).symm
    · intro h
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm ▸ rfl⟩
  simp only [permutationSelector, hmem]

noncomputable def weightedPolyMatrix {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V) (a : Fin k → Fin k → ℝ) :
    Matrix (Fin k) (Fin k) (HahnSeries ℝ (MvPolynomial V ℚ)) :=
  fun i j => HahnSeries.single (a i j) (MvPolynomial.X (v i j))

theorem weightedPolyMatrix_specialize {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    (hahnCoeffRingMap (MvPolynomial.eval (permutationSelector v σ))).mapMatrix
        (weightedPolyMatrix v a) =
      (Matrix.diagonal (fun j => HahnSeries.single (a (σ j) j) (1 : ℚ))).submatrix σ.symm id := by
  classical
  funext i j
  change hahnCoeffRingMap (MvPolynomial.eval (permutationSelector v σ))
      (HahnSeries.single (a i j) (MvPolynomial.X (v i j))) = _
  rw [hahnCoeffRingMap_single, MvPolynomial.eval_X, permutationSelector_apply v hv σ]
  by_cases h : i = σ j
  · subst i
    simp [Matrix.submatrix_apply]
  · have h' : σ.symm i ≠ j := fun hh =>
      h ((σ.apply_symm_apply i).symm.trans (congrArg σ hh))
    simp [Matrix.submatrix_apply, h, h']

theorem weightedPolyMatrix_specialize_det {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    hahnCoeffRingMap (MvPolynomial.eval (permutationSelector v σ))
        (weightedPolyMatrix v a).det =
      (σ.sign : HahnSeries ℝ ℚ) * HahnSeries.single (∑ j, a (σ j) j) (1 : ℚ) := by
  rw [RingHom.map_det, weightedPolyMatrix_specialize v hv a σ,
    Matrix.det_permute, Matrix.det_diagonal]
  rw [show Equiv.Perm.sign σ.symm = σ.sign from Equiv.Perm.sign_inv σ, ← single_sum_one]

theorem weightedPolyMatrix_coeff_ne_zero {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    (weightedPolyMatrix v a).det.coeff (∑ j, a (σ j) j) ≠ 0 := by
  intro hz
  have h := congrArg (fun f : HahnSeries ℝ ℚ => f.coeff (∑ j, a (σ j) j))
    (weightedPolyMatrix_specialize_det v hv a σ)
  rw [hahnCoeffRingMap_coeff, hz, map_zero] at h
  rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs] at h

theorem weighted_generic_det_valuation {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k))
    (hmin : ∀ τ : Equiv.Perm (Fin k), (∑ j, a (σ j) j) ≤ ∑ j, a (τ j) j) :
    HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ))
      ((hahnCoeffRingMap (algebraMap (MvPolynomial V ℚ) (FractionRing (MvPolynomial V ℚ)))).mapMatrix
        (weightedPolyMatrix v a)).det = ((∑ j, a (σ j) j : ℝ) : WithTop ℝ) := by
  let φ : MvPolynomial V ℚ →+* FractionRing (MvPolynomial V ℚ) := algebraMap _ _
  let A := (hahnCoeffRingMap φ).mapMatrix (weightedPolyMatrix v a)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hA : ∀ i j, HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ)) (A i j) =
      (a i j : WithTop ℝ) := by
    intro i j
    change HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ))
      (hahnCoeffRingMap φ (HahnSeries.single (a i j) (MvPolynomial.X (v i j)))) = _
    simpa only [hahnCoeffRingMap_single, HahnSeries.addVal_apply] using
      (HahnSeries.orderTop_single
        ((map_ne_zero_iff φ hφ).mpr (MvPolynomial.X_ne_zero (v i j))))
  change HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ)) A.det = _
  apply le_antisymm
  · change A.det.orderTop ≤ _
    apply HahnSeries.orderTop_le_of_coeff_ne_zero
    dsimp only [A]
    rw [← RingHom.map_det, hahnCoeffRingMap_coeff]
    exact (map_ne_zero_iff φ hφ).mpr (weightedPolyMatrix_coeff_ne_zero v hv a σ)
  · exact weighted_det_valuation_lower A a hA _ hmin

theorem initCols_colDet_valuation_of_minimizing_perm {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (s x : Fin k → M) (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin k))
    (hmin : ∀ τ : Equiv.Perm (Fin k),
      (∑ j, dist (s (σ j)) (x j)) ≤ ∑ j, dist (s (τ j)) (x j)) :
    nu (colDet (initCols s) x) = ((∑ j, dist (s (σ j)) (x j) : ℝ) : WithTop ℝ) := by
  classical
  let v : Fin k → Fin k → Var k M := fun i j => Sum.inl (i, x j)
  let a : Fin k → Fin k → ℝ := fun i j => dist (s i) (x j)
  have hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2) := by
    intro i j hij
    have hp : (i.1, x i.2) = (j.1, x j.2) := Sum.inl.inj hij
    exact Prod.ext (congrArg (fun p : Fin k × M => p.1) hp)
      (hx (congrArg (fun p : Fin k × M => p.2) hp))
  have hmat : (hahnCoeffRingMap (algebraMap (MvPolynomial (Var k M) ℚ) (F k M))).mapMatrix
      (weightedPolyMatrix v a) = Matrix.of (fun i j => initCols s (x j) i) := by
    funext i j
    change hahnCoeffRingMap (algebraMap (MvPolynomial (Var k M) ℚ) (F k M))
      (HahnSeries.single (a i j) (MvPolynomial.X (v i j))) = initCols s (x j) i
    rw [hahnCoeffRingMap_single]
    simp only [initCols, coef, zp, varF, HahnSeries.C_apply,
      HahnSeries.single_mul_single, zero_add, mul_one, a, v]
  have h := weighted_generic_det_valuation v hv a σ hmin
  rw [hmat] at h
  exact h

theorem initCols_self_colDet_valuation {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) (hs : Function.Injective s) :
    nu (colDet (initCols s) s) = 0 := by
  have h := initCols_colDet_valuation_of_minimizing_perm s s hs (Equiv.refl (Fin k))
    (by
      intro τ
      simp only [Equiv.refl_apply, dist_self, Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun _ _ => dist_nonneg))
  simpa only [Equiv.refl_apply, dist_self, Finset.sum_const_zero, WithTop.coe_zero] using h

theorem initCols_workFn_zero {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] (s x : Fin k → M) (hs : Function.Injective s)
    (hx : Function.Injective x) (r : ℕ → M) :
    nu (colDet (initCols s) x) =
      (workFn k (Finset.univ.image s) r 0 (Finset.univ.image x) : WithTop ℝ) := by
  obtain ⟨σ, hdist, hmin⟩ := confDist_images_min_rowPerm s x hs hx
  rw [workFn_zero, hdist]
  exact initCols_colDet_valuation_of_minimizing_perm s x hx σ hmin

end KServerConj
end PaperFile081

section PaperFile082
namespace KServerConj

theorem image_update_injective {k : ℕ} {M : Type*} [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) (r : M) :
    Finset.univ.image (Function.update x i r) =
      insert r ((Finset.univ.image x).erase (x i)) := by
  classical
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_erase]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      exact Or.inl (Function.update_self _ _ _)
    · rw [Function.update_of_ne hji]
      exact Or.inr ⟨fun h => hji (hx h), j, rfl⟩
  · rintro (rfl | ⟨ha, j, hj⟩)
    · exact ⟨i, Function.update_self _ _ _⟩
    · have hji : j ≠ i := fun h => ha (by simpa only [h] using hj.symm)
      exact ⟨j, by rw [Function.update_of_ne hji]; exact hj⟩

theorem update_injective_iff_admissible {k : ℕ} {M : Type*} [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) (r : M) :
    Function.Injective (Function.update x i r) ↔
      r ∉ Finset.univ.image x ∨ x i = r := by
  classical
  constructor
  · intro hu
    by_cases hr : r ∈ Finset.univ.image x
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
      by_cases hji : j = i
      · exact Or.inr (hji ▸ hj)
      · have heq : Function.update x i r j = Function.update x i r i := by
          rw [Function.update_of_ne hji, Function.update_self, hj]
        exact False.elim (hji (hu heq))
    · exact Or.inl hr
  · rintro (hr | hr)
    · exact update_injective_of_not_mem_range x hx r
        (fun ⟨j, hj⟩ => hr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)) i
    · exact (Function.update_eq_self_iff.mpr hr.symm : Function.update x i r = x).symm ▸ hx

end KServerConj
end PaperFile082

section PaperFile083
open scoped BigOperators

namespace KServerConj

theorem determinant_cost_inf_eq_admissible {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M)
    (w : (Fin (n + 1) → M) → ℝ) (b : ℝ)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (x : Fin (n + 1) → M) (hx : Function.Injective x)
    (hle : ∀ i, Function.Injective (Function.update x i r) →
      b ≤ w (Function.update x i r) + dist r (x i))
    (hge : ∃ i, Function.Injective (Function.update x i r) ∧
      w (Function.update x i r) + dist r (x i) ≤ b) :
    Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
      nu (colDet q (Function.update x i r))) = (b : WithTop ℝ) := by
  classical
  apply le_antisymm
  · obtain ⟨i, hi, hcost⟩ := hge
    exact (Finset.inf_le
      (f := fun i => (dist r (x i) : WithTop ℝ) + nu (colDet q (Function.update x i r)))
      (Finset.mem_univ i)).trans (by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr hcost))
  · refine Finset.le_inf ?_
    intro i _
    by_cases hi : Function.Injective (Function.update x i r)
    · simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
        (WithTop.coe_le_coe.mpr (hle i hi))
    · simp only [colDet_eq_zero_of_not_injective q _ hi, nu_zero, WithTop.add_top, le_top]

theorem fresh_request_representation_admissible {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image x) : WithTop ℝ))
    (hfree : ∀ x : Fin (m + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (m + 1) M)) (colDet q x))
    (hr : q (r t) = Pi.single 0 1) :
    ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet (rowReplace q (freshRow r t)) x) =
        (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : WithTop ℝ) := by
  classical
  intro x hx
  have hS : (Finset.univ.image s).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hs]
    simp
  have hX : (Finset.univ.image x).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hx]
    simp
  have hrec := (eq_2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    (Finset.univ.image s) hS r).2 t ht (Finset.univ.image x) hX
  have hle (i : Fin (m + 1)) (hi : Function.Injective (Function.update x i (r t))) :
      workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) ≤
        workFn (m + 1) (Finset.univ.image s) r (t - 1)
          (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) := by
    rw [image_update_injective x hx i (r t)]
    exact hrec.1 (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ((update_injective_iff_admissible x hx i (r t)).mp hi)
  have hge : ∃ i : Fin (m + 1), Function.Injective (Function.update x i (r t)) ∧
      workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) ≤
          workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) := by
    obtain ⟨a, ha, hvalid, heq⟩ := hrec.2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨i, (update_injective_iff_admissible x hx i (r t)).mpr hvalid, ?_⟩
    rw [image_update_injective x hx i (r t)]
    exact heq.ge
  have hcost := determinant_cost_inf_eq_admissible q (r t)
    (fun y => workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image y))
    (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x)) hrep x hx hle hge
  change nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist (r t) y))) x) = _
  exact (fresh_rowReplace_valuation_eq_inf q (r t) t hr hfree x hx).trans hcost

end KServerConj
end PaperFile083

section PaperFile084
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

structure AlgebraicState {k : ℕ} {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (s : Fin k → M) (r : ℕ → M) (t : ℕ) where
  q : M → Fin k → K k M
  represents : ∀ x : Fin k → M, Function.Injective x →
    nu (colDet q x) =
      (workFn k (Finset.univ.image s) r t (Finset.univ.image x) : WithTop ℝ)
  fresh : ∀ u : ℕ, t < u → ∀ x : Fin k → M,
    FreeOf (Set.range fun y : M => (Sum.inr (u, y) : Var k M)) (colDet q x)

noncomputable def initialAlgebraicState {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] (s : Fin k → M) (hs : Function.Injective s) (r : ℕ → M) :
    AlgebraicState s r 0 where
  q := initCols s
  represents := fun x hx => initCols_workFn_zero s x hs hx r
  fresh := by
    intro u _ x
    apply initCols_colDet_freeOf
    intro i y hy
    obtain ⟨z, hz⟩ := hy
    cases hz

noncomputable def AlgebraicState.normalized {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin k → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1) :
    AlgebraicState s r t where
  q := fun y => B.mulVec (st.q y)
  represents := fun x hx =>
    (congrArg nu (colDet_normalize_eq B hB st.q x)).trans (st.represents x hx)
  fresh := fun u hu x => (colDet_normalize_eq B hB st.q x).symm ▸ st.fresh u hu x

noncomputable def AlgebraicState.advance {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s)
    (B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) M))
    (hB : B.det = 1) (hr : B.mulVec (st.q (r (t + 1))) = Pi.single 0 1) :
    AlgebraicState s r (t + 1) where
  q := rowReplace (st.normalized B hB).q (freshRow r (t + 1))
  represents := by
    intro x hx
    exact fresh_request_representation_admissible (Nat.succ_le_succ (Nat.zero_le n))
      s hs r (t + 1) (Nat.succ_le_succ (Nat.zero_le t)) (st.normalized B hB).q
      (fun y hy => by simpa only [Nat.add_sub_cancel] using
        (st.normalized B hB).represents y hy)
      ((st.normalized B hB).fresh (t + 1) (Nat.lt_succ_self t)) hr x hx
  fresh := by
    intro u hu x
    exact fresh_rowReplace_det_freeOf
      (Set.range fun y : M => (Sum.inr (u, y) : Var (n + 2) M))
      (st.normalized B hB).q (r (t + 1)) (t + 1) hr
      ((st.normalized B hB).fresh u ((Nat.lt_succ_self t).trans hu))
      (fun y hy => by
        obtain ⟨z, hz⟩ := hy
        exact (Nat.ne_of_lt hu) (congrArg (fun p : ℕ × M => p.1) (Sum.inr.inj hz)).symm) x

theorem exists_injective_tuple_covering {k : ℕ} {M : Type*}
    (s : Fin k → M) (hs : Function.Injective s) (i₀ : Fin k) (y : M) :
    ∃ x : Fin k → M, Function.Injective x ∧ ∃ i, x i = y := by
  classical
  by_cases hy : y ∈ Set.range s
  · exact ⟨s, hs, hy⟩
  · exact ⟨Function.update s i₀ y, update_injective_of_not_mem_range s hs y hy i₀,
      i₀, Function.update_self _ _ _⟩

theorem AlgebraicState.det_ne_zero {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin k → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (x : Fin k → M) (hx : Function.Injective x) :
    colDet st.q x ≠ 0 := by
  exact (nu_eq_top_iff _).not.mp
    (ne_of_eq_of_ne (st.represents x hx) WithTop.coe_ne_top)

theorem AlgebraicState.column_ne_zero {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin k → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) (i₀ : Fin k) (y : M) :
    st.q y ≠ 0 := by
  obtain ⟨x, hx, i, hi⟩ := exists_injective_tuple_covering s hs i₀ y
  intro hy
  apply st.det_ne_zero x hx
  unfold colDet
  exact Matrix.det_eq_zero_of_column_eq_zero i (fun j => by
    change st.q (x i) j = 0
    rw [hi]
    exact congrFun hy j)

theorem AlgebraicState.exists_normalizer {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) :
    ∃ B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) M),
      B.det = 1 ∧ B.mulVec (st.q (r (t + 1))) = Pi.single 0 1 := by
  exact KServerAlgebra.exists_det_one_normalizer _ (st.column_ne_zero hs 0 _)

end KServerConj
end PaperFile084

section PaperFile085
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

noncomputable def AlgebraicState.chosenNormalizer {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) M) :=
  Classical.choose (st.exists_normalizer hs)

theorem AlgebraicState.chosenNormalizer_spec {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) :
    (st.chosenNormalizer hs).det = 1 ∧
      (st.chosenNormalizer hs).mulVec (st.q (r (t + 1))) = Pi.single 0 1 :=
  Classical.choose_spec (st.exists_normalizer hs)

noncomputable def nextAlgebraicState {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) : AlgebraicState s r (t + 1) :=
  st.advance hs (st.chosenNormalizer hs) (st.chosenNormalizer_spec hs).1
    (st.chosenNormalizer_spec hs).2

noncomputable def algebraicStateSeq {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) :
    (t : ℕ) → AlgebraicState s r t
  | 0 => initialAlgebraicState s hs r
  | t + 1 => nextAlgebraicState (algebraicStateSeq s hs r t) hs

noncomputable def algebraicColumns {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ) :
    M → Fin (n + 2) → K (n + 2) M :=
  (algebraicStateSeq s hs r t).q

noncomputable def algebraicNormalizedColumns {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ) :
    M → Fin (n + 2) → K (n + 2) M :=
  fun x => ((algebraicStateSeq s hs r (t - 1)).chosenNormalizer hs).mulVec
    ((algebraicStateSeq s hs r (t - 1)).q x)

theorem algebraicSequences_isRun {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ) :
    IsRun s r T (algebraicColumns s hs r) (algebraicNormalizedColumns s hs r) := by
  constructor
  · rfl
  · intro t ht _
    cases t with
    | zero => exact (Nat.not_succ_le_zero 0 ht).elim
    | succ u =>
      refine ⟨?_, ?_⟩
      · refine ⟨(algebraicStateSeq s hs r u).chosenNormalizer hs,
          ((algebraicStateSeq s hs r u).chosenNormalizer_spec hs).1, ?_, ?_⟩
        · simpa only [algebraicColumns, Nat.succ_sub_one, Nat.add_sub_cancel] using
            ((algebraicStateSeq s hs r u).chosenNormalizer_spec hs).2
        · intro x
          simp only [algebraicNormalizedColumns, algebraicColumns, Nat.succ_sub_one]
      · rfl

end KServerConj
end PaperFile085

section PaperFile086
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem algebraicState_of_run {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (n + 2) → K (n + 2) M) (hrun : IsRun s r T q qn) :
    ∀ t, t ≤ T → ∃ st : AlgebraicState s r t, st.q = q t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨initialAlgebraicState s hs r, hrun.1.symm⟩
  | succ t ih =>
    intro ht
    obtain ⟨st, hst⟩ := ih ((Nat.le_succ t).trans ht)
    obtain ⟨⟨B, hB, hr, hqn⟩, hupdate⟩ :=
      hrun.2 (t + 1) (Nat.succ_le_succ (Nat.zero_le t)) ht
    have hr' : B.mulVec (st.q (r (t + 1))) = Pi.single 0 1 := by
      simpa only [hst, Nat.add_sub_cancel] using hr
    have hqn' : qn (t + 1) = (st.normalized B hB).q := by
      funext y
      change qn (t + 1) y = B.mulVec (st.q y)
      simpa only [hst, Nat.add_sub_cancel] using hqn y
    refine ⟨st.advance hs B hB hr', ?_⟩
    change rowReplace (st.normalized B hB).q (freshRow r (t + 1)) = q (t + 1)
    rw [hupdate, hqn']

end KServerConj
end PaperFile086

section PaperFile087
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem theorem_2_4 {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ) :
    (∃ q qn : ℕ → M → Fin (m + 1) → K (m + 1) M, IsRun s r T q qn) ∧
    ∀ q qn : ℕ → M → Fin (m + 1) → K (m + 1) M, IsRun s r T q qn →
      ∀ t, t ≤ T → ∀ x : Fin (m + 1) → M, Function.Injective x →
        nu (colDet (q t) x) =
          ((workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : ℝ) : WithTop ℝ) := by
  cases m with
  | zero => exact (Nat.not_succ_le_zero 0 hm).elim
  | succ n =>
    refine ⟨⟨algebraicColumns s hs r, algebraicNormalizedColumns s hs r,
      algebraicSequences_isRun s hs r T⟩, ?_⟩
    intro q qn hrun t ht x hx
    obtain ⟨st, hst⟩ := algebraicState_of_run s hs r T q qn hrun t ht
    simpa only [hst] using st.represents x hx

end KServerConj
end PaperFile087

section PaperFile088
open scoped BigOperators

namespace KServerConj

theorem weightedColumns_rescale {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r y : M) :
    HahnSeries.single (dist r y) (1 : F) • (fun i => weightedColumns q r i y) = q y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, weightedColumns, ← mul_assoc,
    HahnSeries.single_mul_single, add_neg_cancel, one_mul, HahnSeries.single_zero_one]

theorem tupleMinorVal_eq_minorVal {F I J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    DetValuationMilestone.tupleMinorVal (HahnSeries.addVal ℝ F) G = minorVal G := by
  exact (DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) G).trans
      (minorVal_eq_embeddingMinorVal G).symm

theorem projected_weighted_growth_of_cramer_min
    {F : Type*} [Field F] {n : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M) (x : Fin (n + 1) → M)
    (δ β : ℝ)
    (hδ : HahnSeries.addVal ℝ F (Matrix.of fun i j => q (x j) i).det = (δ : WithTop ℝ))
    (hβ : (Finset.univ.inf fun i => HahnSeries.addVal ℝ F
      (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
        HahnSeries.single (dist r (x i)) (1 : F))) = (β : WithTop ℝ)) :
    ∃ a b : ℝ,
      minorVal (weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      β - δ ≤ b - a := by
  have hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (ne_of_eq_of_ne hδ WithTop.coe_ne_top)
  obtain ⟨δ', α', a, b, hδ', hα', ha, hb, hgrow⟩ :=
    DetValuationMilestone.canonical_projected_minValue_growth
      (HahnSeries.addVal ℝ F) (fun _ => HahnSeries.orderTop_eq_top)
      (fun f g => AddValuation.map_mul _ f g)
      (fun f g => AddValuation.map_add _ f g)
      (Matrix.of fun i j => q (x j) i) (weightedColumns q r) x
      (fun i => HahnSeries.single (dist r (x i)) (1 : F))
      (fun i => (weightedColumns_rescale q r (x i)).symm) hdet
  exact ⟨a, b,
    (tupleMinorVal_eq_minorVal (weightedColumns q r)).symm.trans ha,
    (tupleMinorVal_eq_minorVal ((weightedColumns q r).submatrix Fin.succ id)).symm.trans hb,
    by simpa only [WithTop.coe_inj.mp (hδ'.symm.trans hδ),
      WithTop.coe_inj.mp (hα'.symm.trans hβ)] using hgrow⟩

theorem fresh_rowReplace_valuation_eq_cramerMin {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ x : Fin (n + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) (colDet q x))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      Finset.univ.inf (fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) := by
  exact (fresh_rowReplace_valuation_eq_inf q r t hr hfree x hx).trans
    (Finset.inf_congr rfl fun i _ => by
      simp only [← hr, KServerAlgebra.updateCol_column_family, nu_mul, nu_zp, colDet,
        add_comm])

theorem request_projected_minor_growth {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) (δ β : ℝ)
    (hδ : nu (colDet q x) = (δ : WithTop ℝ))
    (hβ : nu (colDet (rowReplace q
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) = (β : WithTop ℝ)) :
    ∃ a b : ℝ,
      minorVal (weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      β - δ ≤ b - a := by
  exact projected_weighted_growth_of_cramer_min q r x δ β hδ
    ((fresh_rowReplace_valuation_eq_cramerMin q r t hr hfree x hx).symm.trans hβ)

end KServerConj
end PaperFile088

section PaperFile089
open scoped BigOperators

namespace KServerConj

theorem det_updateCol_e0 {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (j : Fin (n + 1)) :
    (A.updateCol j (Pi.single 0 1)).det =
      (-1 : R) ^ j.val * (A.submatrix Fin.succ j.succAbove).det := by
  rw [Matrix.det_succ_column _ j]
  simp [Matrix.updateCol, Function.update, Pi.single_apply, mul_ite, ite_mul,
    Matrix.submatrix, Fin.succAbove_ne]

theorem scaled_cramer_factor {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A H : Matrix ι ι R) (c : ι → R) (v : ι → R)
    (hcol : ∀ a j, A a j = c j * H a j) (i : ι) :
    (A.updateCol i v).det * c i = (∏ j, c j) * (H.updateCol i v).det := by
  calc
    _ = (A.updateCol i (c i • v)).det := by
      simpa only [mul_comm] using (Matrix.det_updateCol_smul A i (c i) v).symm
    _ = (Matrix.of (fun a j => c j * (H.updateCol i v) a j)).det := by
      apply congrArg Matrix.det
      ext a j
      by_cases hj : j = i <;>
        simp [Matrix.updateCol, Function.update, hj, hcol, Pi.smul_apply, smul_eq_mul]
    _ = _ := Matrix.det_mul_row c (H.updateCol i v)

theorem projected_minor_le_cramer {F : Type*} [Field F] {n : ℕ} {M : Type*} [Fintype M]
    (H : Matrix (Fin (n + 1)) M (HahnSeries ℝ F)) (x : Fin (n + 1) → M)
    (j : Fin (n + 1)) :
    minorVal (H.submatrix Fin.succ id) ≤
      HahnSeries.addVal ℝ F ((H.submatrix id x).updateCol j (Pi.single 0 1)).det := by
  rw [det_updateCol_e0]
  simp only [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_neg,
    AddValuation.map_one, nsmul_zero, zero_add]
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
    minorVal_le_tuple (H.submatrix Fin.succ id) (x ∘ j.succAbove)

theorem weighted_cramer_ge_projected {n : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (x : Fin (n + 1) → M)
    (b : ℝ)
    (hb : minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ))
    (i : Fin (n + 1)) :
    (((∑ j, dist r (x j)) + b : ℝ) : WithTop ℝ) ≤
      nu (((Matrix.of fun a j => q (x j) a).updateCol i (Pi.single 0 1)).det *
        zp (dist r (x i))) := by
  have hcol (a j : Fin (n + 1)) : q (x j) a =
      (zp (dist r (x j)) : K (n + 1) M) * weightedColumns q r a (x j) := by
    exact (congrFun (weightedColumns_rescale q r (x j)) a).symm
  have hfac := scaled_cramer_factor (Matrix.of fun a j => q (x j) a)
    ((weightedColumns q r).submatrix id x) (fun j => (zp (dist r (x j)) : K (n + 1) M))
    (Pi.single 0 1) hcol i
  rw [hfac, nu_mul, ← zp_sum Finset.univ (fun j => dist r (x j)), nu_zp, WithTop.coe_add]
  exact add_le_add le_rfl (hb.symm.trans_le (projected_minor_le_cramer (weightedColumns q r) x i))

theorem weighted_det_valuation {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (x : Fin (n + 1) → M)
    (a : ℝ)
    (ha : nu ((weightedColumns q r).submatrix id x).det = (a : WithTop ℝ)) :
    nu (colDet q x) = (((∑ j, dist r (x j)) + a : ℝ) : WithTop ℝ) := by
  have hA : (Matrix.of fun i j => q (x j) i) =
      Matrix.of (fun i j => (zp (dist r (x j)) : K (n + 1) M) *
        ((weightedColumns q r).submatrix id x) i j) := by
    apply Matrix.ext
    intro i j
    exact (congrFun (weightedColumns_rescale q r (x j)) i).symm
  change nu (Matrix.of (fun i j => q (x j) i)).det = _
  rw [hA, Matrix.det_mul_row, nu_mul, ← zp_sum Finset.univ (fun j => dist r (x j)),
    nu_zp, ha, ← WithTop.coe_add]

end KServerConj
end PaperFile089

section PaperFile090
namespace KServerConj

theorem exists_injective_enumeration {M : Type*} [DecidableEq M] {k : ℕ}
    (X : Finset M) (hX : X.card = k) :
    ∃ x : Fin k → M, Function.Injective x ∧ Finset.univ.image x = X := by
  classical
  let e : X ≃ Fin k := X.equivFinOfCardEq hX
  let x : Fin k → M := fun i => (e.symm i).val
  have hx : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  refine ⟨x, hx, ?_⟩
  apply Finset.ext
  intro a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).property
  · intro ha
    refine ⟨e ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)

end KServerConj
end PaperFile090

section PaperFile091
open scoped BigOperators

namespace KServerConj

theorem projected_minor_growth_bound {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M)
    (s : Fin (m + 1) → M) (hs : Function.Injective s) (w w' : Finset M → ℝ)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (hcost : ∀ x : Fin (m + 1) → M, Function.Injective x →
      (Finset.univ.inf fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) = (w' (Finset.univ.image x) : WithTop ℝ)) :
    ∃ a b : ℝ, minorVal (weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      ∀ x : Fin (m + 1) → M, Function.Injective x →
        w' (Finset.univ.image x) - w (Finset.univ.image x) ≤ b - a := by
  obtain ⟨a, b, ha, hb, _⟩ := projected_weighted_growth_of_cramer_min q r s
    (w (Finset.univ.image s)) (w' (Finset.univ.image s)) (hrep s hs) (hcost s hs)
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx
  obtain ⟨a', b', ha', hb', hg⟩ := projected_weighted_growth_of_cramer_min q r x
    (w (Finset.univ.image x)) (w' (Finset.univ.image x)) (hrep x hx) (hcost x hx)
  have hea : a' = a := WithTop.coe_inj.mp (ha'.symm.trans ha)
  have heb : b' = b := WithTop.coe_inj.mp (hb'.symm.trans hb)
  simpa only [hea, heb] using hg

theorem projected_minor_growth_attained {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M) (w w' : Finset M → ℝ)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (hcost : ∀ x : Fin (m + 1) → M, Function.Injective x →
      (Finset.univ.inf fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) = (w' (Finset.univ.image x) : WithTop ℝ))
    (a b : ℝ) (ha : minorVal (weightedColumns q r) = (a : WithTop ℝ))
    (hb : minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ)) :
    ∃ x : Fin (m + 1) → M, Function.Injective x ∧
      b - a ≤ w' (Finset.univ.image x) - w (Finset.univ.image x) := by
  obtain ⟨x, hxmin⟩ := exists_minorVal_minimizer (weightedColumns q r) a ha
  have hnew : (((∑ j, dist r (x j)) + b : ℝ) : WithTop ℝ) ≤
      (w' (Finset.univ.image x) : WithTop ℝ) := by
    rw [← hcost x x.injective]
    exact Finset.le_inf (fun i _ => weighted_cramer_ge_projected q r x b hb i)
  have hold : w (Finset.univ.image x) = (∑ j, dist r (x j)) + a :=
    WithTop.coe_inj.mp ((hrep x x.injective).symm.trans
      (weighted_det_valuation q r x a hxmin))
  refine ⟨x, x.injective, ?_⟩
  have hnew_real := WithTop.coe_le_coe.mp hnew
  linarith only [hold, hnew_real]

theorem projected_extendedCost_eq {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M)
    (s : Fin (m + 1) → M) (hs : Function.Injective s) (w w' : Finset M → ℝ)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (hcost : ∀ x : Fin (m + 1) → M, Function.Injective x →
      (Finset.univ.inf fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) = (w' (Finset.univ.image x) : WithTop ℝ)) :
    ∃ a b : ℝ, minorVal (weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      (⨆ X : {X : Finset M // X.card = m + 1}, w' X.val - w X.val) = b - a := by
  classical
  have hS : (Finset.univ.image s).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hs]
    simp
  letI : Nonempty {X : Finset M // X.card = m + 1} := ⟨⟨Finset.univ.image s, hS⟩⟩
  obtain ⟨a, b, ha, hb, hupper⟩ := projected_minor_growth_bound q r s hs w w' hrep hcost
  refine ⟨a, b, ha, hb, le_antisymm ?_ ?_⟩
  · apply ciSup_le
    intro X
    obtain ⟨x, hx, himage⟩ := exists_injective_enumeration X.val X.property
    simpa only [himage] using hupper x hx
  · obtain ⟨x, hx, hgrow⟩ := projected_minor_growth_attained q r w w' hrep hcost a b ha hb
    have hX : (Finset.univ.image x).card = m + 1 := by
      rw [Finset.card_image_of_injective _ hx]
      simp
    exact hgrow.trans (le_ciSup (Finite.bddAbove_range
      (fun X : {X : Finset M // X.card = m + 1} => w' X.val - w X.val))
      ⟨Finset.univ.image x, hX⟩)

end KServerConj
end PaperFile091

section PaperFile092
open scoped BigOperators

namespace KServerConj

theorem request_cramer_min_eq_workFn {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image x) : WithTop ℝ))
    (hr : q (r t) = Pi.single 0 1) (x : Fin (m + 1) → M) (hx : Function.Injective x) :
    (Finset.univ.inf fun i => nu
      (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
        zp (dist (r t) (x i)))) =
      (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : WithTop ℝ) := by
  classical
  have hS : (Finset.univ.image s).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hs]
    simp
  have hX : (Finset.univ.image x).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hx]
    simp
  have hrec := (eq_2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    (Finset.univ.image s) hS r).2 t ht (Finset.univ.image x) hX
  have hle (i : Fin (m + 1)) (hi : Function.Injective (Function.update x i (r t))) :
      workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) ≤
        workFn (m + 1) (Finset.univ.image s) r (t - 1)
          (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) := by
    rw [image_update_injective x hx i (r t)]
    exact hrec.1 (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ((update_injective_iff_admissible x hx i (r t)).mp hi)
  have hge : ∃ i : Fin (m + 1), Function.Injective (Function.update x i (r t)) ∧
      workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) ≤
          workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) := by
    obtain ⟨a, ha, hvalid, heq⟩ := hrec.2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨i, (update_injective_iff_admissible x hx i (r t)).mpr hvalid, ?_⟩
    rw [image_update_injective x hx i (r t)]
    exact heq.ge
  have hcost := determinant_cost_inf_eq_admissible q (r t)
    (fun y => workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image y))
    (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x)) hrep x hx hle hge
  refine (Finset.inf_congr rfl (fun i _ => ?_)).trans hcost
  simp only [← hr, KServerAlgebra.updateCol_column_family, nu_mul, nu_zp, colDet, add_comm]

end KServerConj
end PaperFile092

section PaperFile094
set_option autoImplicit false

namespace KServerConj

theorem lemma_4_3 {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = ((workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image x) : ℝ) :
        WithTop ℝ))
    (hr : q (r t) = Pi.single 0 1) :
    ∃ a b : ℝ, minorVal (Hmat q (r t)) = (a : WithTop ℝ) ∧ minorVal (Hhat q (r t)) = (b : WithTop ℝ) ∧
      extCost (m + 1) (Finset.univ.image s) r t = b - a := by
  change ∃ a b : ℝ, minorVal (weightedColumns q (r t)) = (a : WithTop ℝ) ∧
    minorVal ((weightedColumns q (r t)).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      (⨆ X : {X : Finset M // X.card = m + 1},
        workFn (m + 1) (Finset.univ.image s) r t X.val -
          workFn (m + 1) (Finset.univ.image s) r (t - 1) X.val) = b - a
  exact projected_extendedCost_eq q (r t) s hs
    (fun X => workFn (m + 1) (Finset.univ.image s) r (t - 1) X)
    (fun X => workFn (m + 1) (Finset.univ.image s) r t X) hrep
    (fun x hx => request_cramer_min_eq_workFn s hs r t ht q hrep hr x hx)

end KServerConj
end PaperFile094

section PaperFile095
open scoped BigOperators

namespace KServerConj

theorem quadraticMatrix_normalize {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M]
    (B : Matrix (Fin k) (Fin k) (HahnSeries ℝ F))
    (q : M → Fin k → HahnSeries ℝ F) :
    quadraticMatrix (fun y => B.mulVec (q y)) = sym2Mat B * quadraticMatrix q := by
  funext p c
  induction c using Sym2.ind with
  | _ x y =>
    exact (congrFun ((Matrix.mulVec_smul (sym2Mat B)
      (HahnSeries.single (-dist x y) (1 : F)) (symProd (q x) (q y))).trans
        (congrArg (fun v => HahnSeries.single (-dist x y) (1 : F) • v)
          (sym2Mat_mulVec_symProd B (q x) (q y)))) p).symm

theorem minorVal_quadraticMatrix_normalize {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (B : Matrix (Fin k) (Fin k) (HahnSeries ℝ F)) (hB : B.det = 1)
    (q : M → Fin k → HahnSeries ℝ F) :
    minorVal (quadraticMatrix (fun y => B.mulVec (q y))) = minorVal (quadraticMatrix q) := by
  simpa only [quadraticMatrix_normalize, det_sym2Mat, hB, one_pow,
    AddValuation.map_one, zero_add] using minorVal_mul (sym2Mat B) (quadraticMatrix q)

theorem Psi_normalize {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1)
    (q : M → Fin k → K k M) :
    Psi (fun y => B.mulVec (q y)) = Psi q := by
  exact minorVal_quadraticMatrix_normalize B hB q

end KServerConj
end PaperFile095

section PaperFile096
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem corollary_4_4 {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (m + 1) → K (m + 1) M) (hrun : IsRun s r T q qn) :
    ∀ t, 1 ≤ t → t ≤ T →
      ((extCost (m + 1) (Finset.univ.image s) r t : ℝ) : WithTop ℝ) + Psi (q (t - 1)) ≤
        Psi (q t) := by
  intro t ht htT
  obtain ⟨⟨B, hB, hr, hqn⟩, hupdate⟩ := hrun.2 t ht htT
  have hqn' : qn t = fun y => B.mulVec (q (t - 1) y) := funext hqn
  have hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet (qn t) x) =
        (workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image x) : WithTop ℝ) := by
    intro x hx
    rw [hqn', colDet_normalize_eq B hB]
    exact (theorem_2_4 hm s hs r T).2 q qn hrun (t - 1) ((Nat.sub_le t 1).trans htT) x hx
  have hrq : qn t (r t) = Pi.single 0 1 := by rw [hqn']; exact hr
  obtain ⟨a, b, ha, hb, hext⟩ := lemma_4_3 hm s hs r t ht (qn t) hrep hrq
  have hδ : ∀ x, nu (freshRow (m := m) r t x) = (dist (r t) x : WithTop ℝ) := by
    intro x
    simp only [freshRow, nu_mul, nu_coef, nu_zp, zero_add]
  have hpay := potential_pays_of_projected_values hm (qn t) (r t) hrq (freshRow r t)
    hδ a b ha hb
  have hPsi : Psi (q (t - 1)) = Psi (qn t) := by
    rw [hqn']
    exact (Psi_normalize B hB (q (t - 1))).symm
  rw [hext, hPsi, hupdate]
  exact hpay

end KServerConj
end PaperFile096

section PaperFile097
open scoped BigOperators

namespace KServerConj

theorem negPairDist_map_succ {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin (k + 1) → M) (p : Sym2 (Fin k)) :
    negPairDist x (p.map Fin.succ) = negPairDist (fun i => x i.succ) p := by
  induction p using Sym2.ind with
  | _ i j => rfl

theorem twice_sum_negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) :
    2 * (∑ p, negPairDist x p) = -(∑ i, ∑ j, dist (x i) (x j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : (∑ p, negPairDist x p) =
        (∑ i : Fin (k + 1), -dist (x 0) (x i)) +
          ∑ p, negPairDist (fun i : Fin k => x i.succ) p := by
      calc
        _ = ∑ p : Fin (k + 1) ⊕ Sym2 (Fin k),
            negPairDist x ((sym2FinSuccEquiv k).symm p) :=
          Fintype.sum_equiv (sym2FinSuccEquiv k) _ _ (fun p => by simp)
        _ = _ := by
          simp only [Fintype.sum_sum_type, sym2FinSuccEquiv_symm_inl,
            sym2FinSuccEquiv_symm_inr, negPairDist_map_succ]
          rfl
    have hfull : (∑ i, ∑ j, dist (x i) (x j)) =
        2 * (∑ i : Fin k, dist (x 0) (x i.succ)) +
          ∑ i : Fin k, ∑ j : Fin k, dist (x i.succ) (x j.succ) := by
      simp only [Fin.sum_univ_succ, dist_self, zero_add, Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun i _ => dist_comm (x i.succ) (x 0))]
      ring
    simp only [Fin.sum_univ_succ, dist_self, zero_add,
      Finset.sum_neg_distrib] at hsplit
    have htail := ih (fun i => x i.succ)
    linarith only [hsplit, hfull, htail]

theorem sum_offDiag_dist {M : Type*} [PseudoMetricSpace M] (X : Finset M) :
    (∑ p ∈ X.offDiag, dist p.1 p.2) = ∑ i ∈ X, ∑ j ∈ X, dist i j := by
  classical
  calc
    _ = ∑ p ∈ X ×ˢ X, dist p.1 p.2 := by
      apply Finset.sum_subset
      · intro p hp
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_offDiag.mp hp).1, (Finset.mem_offDiag.mp hp).2.1⟩
      · intro p hp hn
        have heq : p.1 = p.2 := by
          by_contra h
          exact hn (Finset.mem_offDiag.mpr
            ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2, h⟩)
        simp only [heq, dist_self]
    _ = _ := Finset.sum_product X X (fun p => dist p.1 p.2)

theorem sum_negPairDist_eq_neg_cl {k : ℕ} {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) :
    (∑ p, negPairDist x p) = -cl (Finset.univ.image x) := by
  classical
  unfold cl
  rw [sum_offDiag_dist]
  simp only [Finset.sum_image (fun i _ j _ h => hx h)]
  have h := twice_sum_negPairDist x
  linarith only [h]

theorem minorVal_quadratic_le_clique {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (hx : Function.Injective x)
    (δ : ℝ) (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    minorVal (quadraticMatrix q) ≤
      ((((k : ℝ) + 1) * δ - cl (Finset.univ.image x) : ℝ) : WithTop ℝ) := by
  have h := quadraticMatrix_selected_valuation q x δ hD
  rw [sum_negPairDist_eq_neg_cl x hx] at h
  simpa only [sub_eq_add_neg, add_comm] using
    (minorVal_le_tuple (quadraticMatrix q) (Sym2.map x)).trans_eq h

end KServerConj
end PaperFile097

section PaperFile098
namespace KServerConj

theorem terminal_bound_of_representation {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → K k M) (w : Finset M → ℝ)
    (hrep : ∀ x : Fin k → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (X : Finset M) (hX : X.card = k) :
    Psi q ≤ ((((k : ℝ) + 1) * w X - cl X : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx, himage⟩ := exists_injective_enumeration X hX
  change minorVal (quadraticMatrix q) ≤ _
  simpa only [himage] using
    minorVal_quadratic_le_clique q x hx (w (Finset.univ.image x)) (hrep x hx)

end KServerConj
end PaperFile098

section PaperFile099
set_option autoImplicit false

namespace KServerConj

theorem lemma_5_1 {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (m + 1) → K (m + 1) M) (hrun : IsRun s r T q qn) :
    ∀ t, t ≤ T → ∀ X : Finset M, X.card = m + 1 →
      Psi (q t) ≤
        ((((m + 2 : ℕ) : ℝ) * workFn (m + 1) (Finset.univ.image s) r t X - cl X : ℝ) : WithTop ℝ) := by
  intro t ht X hX
  have h := terminal_bound_of_representation (q t)
    (fun Y => workFn (m + 1) (Finset.univ.image s) r t Y)
    (fun x hx => (theorem_2_4 hm s hs r T).2 q qn hrun t ht x hx) X hX
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
    one_add_one_eq_two] using h

end KServerConj
end PaperFile099

section PaperFile100
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem dist_sub_dist_initial_le {M : Type*} [PseudoMetricSpace M]
    (a b x y : M) : dist x y - dist a b ≤ dist a x + dist b y := by
  linarith [dist_triangle x a y, dist_triangle a b y, dist_comm x a]

theorem nu_initCols_entry {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) (x : M) (i : Fin k) :
    nu (initCols s x i) = (dist (s i) x : WithTop ℝ) := by
  simp only [initCols, nu_mul, nu_coef, nu_zp, zero_add]

theorem initial_product_lower_bound {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) (x y : M) (i j : Fin k) :
    ((dist x y - dist (s i) (s j) : ℝ) : WithTop ℝ) ≤
      nu (initCols s x i * initCols s y j) := by
  simpa only [nu_mul, nu_initCols_entry, ← WithTop.coe_add] using
    (WithTop.coe_le_coe.mpr (dist_sub_dist_initial_le (s i) (s j) x y))

theorem initial_symProd_lower_bound {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) (x y : M) (p : Sym2 (Fin k)) :
    ((dist x y + negPairDist s p : ℝ) : WithTop ℝ) ≤
      nu (symProd (initCols s x) (initCols s y) p) := by
  induction p using Sym2.ind with
  | _ i j =>
    by_cases hij : i = j
    · subst j
      simpa only [negPairDist, Sym2.lift_mk, symProd, if_pos rfl, ite_true,
        sub_eq_add_neg] using initial_product_lower_bound s x y i i
    · simp only [symProd, Sym2.lift_mk, if_neg hij]
      apply AddValuation.map_le_add (HahnSeries.addVal ℝ (F k M))
      · simpa only [negPairDist, Sym2.lift_mk, sub_eq_add_neg] using
          initial_product_lower_bound s x y i j
      · simpa only [negPairDist, Sym2.lift_mk, sub_eq_add_neg, dist_comm (s j) (s i)] using
          initial_product_lower_bound s x y j i

theorem initial_quadratic_entry_lower_bound {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) (p : Sym2 (Fin k)) (c : Sym2 M) :
    (negPairDist s p : WithTop ℝ) ≤ nu (quadraticMatrix (initCols s) p c) := by
  induction c using Sym2.ind with
  | _ x y =>
    have hb := initial_symProd_lower_bound s x y p
    calc
      (negPairDist s p : WithTop ℝ) =
          ((-dist x y : ℝ) : WithTop ℝ) +
            ((dist x y + negPairDist s p : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add]
        congr 1
        ring
      _ ≤ ((-dist x y : ℝ) : WithTop ℝ) +
          nu (symProd (initCols s x) (initCols s y) p) := add_le_add le_rfl hb
      _ = nu (quadraticMatrix (initCols s) p s(x, y)) := by
        change _ = nu (zp (-dist x y) * symProd (initCols s x) (initCols s y) p)
        rw [nu_mul, nu_zp]

noncomputable def initialQuadraticScale {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) : Matrix (Sym2 (Fin k)) (Sym2 (Fin k)) (K k M) := by
  classical
  exact Matrix.diagonal (fun p => zp (-negPairDist s p))

theorem initial_scaled_entry_nonneg {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) (p : Sym2 (Fin k)) (c : Sym2 M) :
    (0 : WithTop ℝ) ≤
      nu ((initialQuadraticScale s * quadraticMatrix (initCols s)) p c) := by
  classical
  rw [initialQuadraticScale, Matrix.diagonal_mul, nu_mul, nu_zp]
  calc
    (0 : WithTop ℝ) = ((-negPairDist s p : ℝ) : WithTop ℝ) +
        (negPairDist s p : WithTop ℝ) := by
      rw [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]
    _ ≤ _ := add_le_add le_rfl (initial_quadratic_entry_lower_bound s p c)

theorem initial_scale_det_valuation {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] (s : Fin k → M) (hs : Function.Injective s) :
    nu (initialQuadraticScale s).det = (cl (Finset.univ.image s) : WithTop ℝ) := by
  classical
  rw [initialQuadraticScale, Matrix.det_diagonal, ← zp_sum, nu_zp,
    Finset.sum_neg_distrib, sum_negPairDist_eq_neg_cl s hs, neg_neg]

theorem initial_potential_lower_bound {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] (s : Fin k → M) (hs : Function.Injective s) :
    ((-cl (Finset.univ.image s) : ℝ) : WithTop ℝ) ≤ Psi (initCols s) := by
  classical
  have hscaled : (0 : WithTop ℝ) ≤
      minorVal (initialQuadraticScale s * quadraticMatrix (initCols s)) := by
    rw [minorVal_eq_embeddingMinorVal]
    exact DetValuationMilestone.zero_le_embeddingMinorVal_of_entries
      (HahnSeries.addVal ℝ (F k M)) (AddValuation.map_zero _) (AddValuation.map_one _)
      (fun a => AddValuation.map_neg _ a) (fun a b => AddValuation.map_mul _ a b)
      (fun a b => AddValuation.map_add _ a b)
      (initialQuadraticScale s * quadraticMatrix (initCols s)) (initial_scaled_entry_nonneg s)
  rw [minorVal_mul] at hscaled
  have hdiag : HahnSeries.addVal ℝ (F k M) (initialQuadraticScale s).det =
      (cl (Finset.univ.image s) : WithTop ℝ) := initial_scale_det_valuation s hs
  rw [hdiag] at hscaled
  change ((-cl (Finset.univ.image s) : ℝ) : WithTop ℝ) ≤
    minorVal (quadraticMatrix (initCols s))
  apply WithTop.le_of_add_le_add_left (x := (cl (Finset.univ.image s) : WithTop ℝ)) (by simp)
  simpa only [← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero] using hscaled

theorem initial_potential_eq_neg_cl {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] (s : Fin k → M) (hs : Function.Injective s) :
    Psi (initCols s) = ((-cl (Finset.univ.image s) : ℝ) : WithTop ℝ) := by
  apply le_antisymm _ (initial_potential_lower_bound s hs)
  change minorVal (quadraticMatrix (initCols s)) ≤ _
  have hD : HahnSeries.addVal ℝ (F k M)
      (Matrix.of fun i j => initCols s (s j) i).det = (0 : WithTop ℝ) :=
    initCols_self_colDet_valuation s hs
  simpa only [mul_zero, zero_sub] using
    minorVal_quadratic_le_clique (initCols s) s hs 0 hD

end KServerConj
end PaperFile100

section PaperFile101
namespace KServerConj

theorem lemma_5_2 {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) :
    Psi (initCols s) = ((-(cl (Finset.univ.image s)) : ℝ) : WithTop ℝ) := by
  exact initial_potential_eq_neg_cl s hs

end KServerConj
end PaperFile101

section PaperFile102
open scoped BigOperators

namespace KServerConj

theorem extended_cost_bound_of_run {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (m + 1) → K (m + 1) M) (hrun : IsRun s r T q qn)
    (XT : Finset M) (hXT : XT.card = m + 1) :
    (∑ t ∈ Finset.Icc 1 T, extCost (m + 1) (Finset.univ.image s) r t) ≤
      (((m + 1 : ℕ) : ℝ) + 1) * workFn (m + 1) (Finset.univ.image s) r T XT +
        cl (Finset.univ.image s) - cl XT := by
  have hpaid := payment_telescope
    (fun t => extCost (m + 1) (Finset.univ.image s) r t) (fun t => Psi (q t)) T
    (corollary_4_4 hm s hs r T q qn hrun)
  rw [hrun.1, lemma_5_2 hm s hs] at hpaid
  have hend := lemma_5_1 hm s hs r T q qn hrun T le_rfl XT hXT
  have hbound := hpaid.trans hend
  rw [← WithTop.coe_add] at hbound
  have hreal := WithTop.coe_le_coe.mp hbound
  have hcoeff : ((m + 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by
    norm_num [Nat.cast_add, add_assoc]
  rw [hcoeff] at hreal
  linarith only [hreal]

end KServerConj
end PaperFile102

section PaperFile103
open scoped BigOperators

namespace KServerConj

theorem wfaCost_succ {M : Type*} [PseudoMetricSpace M] (C : ℕ → Finset M) (t : ℕ) :
    wfaCost C (t + 1) = wfaCost C t + confDist (C t) (C (t + 1)) := by
  simpa only [wfaCost, Nat.add_sub_cancel] using
    Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1)
      (fun s => confDist (C (s - 1)) (C s))

theorem workFn_growth_le_extCost {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M) (hX : X.card = k) :
    workFn k C₀ r t X - workFn k C₀ r (t - 1) X ≤ extCost k C₀ r t := by
  classical
  exact le_ciSup (Set.finite_range
    (fun Y : {Y : Finset M // Y.card = k} =>
      workFn k C₀ r t Y.1 - workFn k C₀ r (t - 1) Y.1)).bddAbove ⟨X, hX⟩

theorem wfa_step_accounting {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (T : ℕ) (C : ℕ → Finset M) (hC : IsWFATraj k C₀ r T C)
    (t : ℕ) (ht : 1 ≤ t) (hT : t ≤ T) :
    confDist (C (t - 1)) (C t) + workFn k C₀ r t (C t) -
      workFn k C₀ r (t - 1) (C (t - 1)) ≤ extCost k C₀ r t := by
  have heq := hC.objective_eq k hk C₀ hC₀ r T C t ht hT
  have hg := workFn_growth_le_extCost k C₀ r t (C (t - 1))
    (hC.card hC₀ (t - 1) ((Nat.sub_le t 1).trans hT))
  linarith

end KServerConj
end PaperFile103

section PaperFile104
open scoped BigOperators
set_option autoImplicit false

namespace KServerConj

theorem lemma_1_1 {M : Type*} [PseudoMetricSpace M] [Fintype M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) (C : ℕ → Finset M)
    (hC : IsWFATraj k C₀ r T C) :
    wfaCost C T + workFn k C₀ r T (C T) ≤ ∑ t ∈ Finset.Icc 1 T, extCost k C₀ r t := by
  induction T generalizing C with
  | zero => simp [wfaCost, workFn_zero, hC.1, confDist_self]
  | succ T ih =>
    have hp := ih C (hC.mono (Nat.le_succ T))
    have hs := wfa_step_accounting k hk C₀ hC₀ r (T + 1) C hC (T + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hs
    rw [wfaCost_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1)]
    linarith

end KServerConj
end PaperFile104

section PaperFile105
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem theorem_5_3 {M : Type*} [PseudoMetricSpace M] [Fintype M] (k : ℕ) (hk : 2 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) (XT : Finset M) (hXT : XT.card = k)
    (hmin : ∀ X : Finset M, X.card = k → workFn k C₀ r T XT ≤ workFn k C₀ r T X) :
    (∑ t ∈ Finset.Icc 1 T, extCost k C₀ r t ≤
        ((k : ℝ) + 1) * workFn k C₀ r T XT + cl C₀ - cl XT) ∧
    ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
      wfaCost C T ≤ (k : ℝ) * workFn k C₀ r T XT + cl C₀ - cl XT := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, (Nat.sub_add_cancel hk).symm⟩
  obtain ⟨s, hs, hsimage⟩ := exists_injective_enumeration C₀ hC₀
  have hm : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  obtain ⟨q, qn, hrun⟩ := (theorem_2_4 hm s hs r T).1
  have hExt := extended_cost_bound_of_run hm s hs r T q qn hrun XT hXT
  rw [hsimage] at hExt
  refine ⟨hExt, ?_⟩
  intro C hC
  have hk1 : 1 ≤ n + 2 := Nat.succ_le_succ (Nat.zero_le (n + 1))
  have haccount := lemma_1_1 (n + 2) hk1 C₀ hC₀ r T C hC
  have hCT : (C T).card = n + 2 := by
    by_cases hT : T = 0
    · simpa only [hT, hC.1] using hC₀
    · exact (hC.2 T (Nat.one_le_iff_ne_zero.mpr hT) le_rfl).1
  have hminCT := hmin (C T) hCT
  linarith only [hExt, haccount, hminCT]

end KServerConj
end PaperFile105

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) :
    (∃ C : ℕ → Finset M, IsWFATraj k C₀ r T C) ∧
    ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
      wfaCost C T ≤ (k : ℝ) * opt k C₀ r T + cl C₀  := by
  classical
  exact arbitrary_space_theorem_of_finite_bound k hk
    (fun hk₂ G A hA q S D hD =>
      finite_wfa_bound_of_endpoint k hk A hA q S
        (fun XT hXT hmin C hC => (theorem_5_3 k hk₂ A hA q S XT hXT hmin).2 C hC)
        D hD) C₀ hC₀ r T

#print axioms solution
