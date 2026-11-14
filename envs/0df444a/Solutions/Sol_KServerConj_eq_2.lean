-- Prove2me | solution 1 for KServerConj.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:01:44.127484+00:00
-- url     : https://prove2.me/submissions/36ec2b5f-f59c-4477-a458-be8160225eb5

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_confDist
import Definitions.Def_KServerConj_workFn
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
end PaperFile002

section PaperFile004
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
end PaperFile004

section PaperFile005
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
end PaperFile005

section PaperFile006
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
end PaperFile006

section PaperFile007
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
end PaperFile007

section PaperFile008
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
end PaperFile008

section PaperFile009
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
end PaperFile009

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] [DecidableEq M] (k : ℕ) (hk : 1 ≤ k)
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

#print axioms solution
