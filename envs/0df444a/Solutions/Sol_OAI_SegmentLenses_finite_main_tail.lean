-- Prove2me | solution 1 for OAI.SegmentLenses.finite_main_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:48:34.601331+00:00
-- url     : https://prove2.me/submissions/85163aee-1f0c-4af9-a263-15bf01903069

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/TailBudget.lean:L224-L286
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.finite_main_tail. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery
import Theorems.Thm_OAI_SegmentLenses_exists_atomic_law
import Theorems.Thm_OAI_SegmentLenses_exists_norming_head
import Theorems.Thm_OAI_SegmentLenses_represented_joint_bound

-- ---- from OAI.Analysis.SegmentLenses.LawRecovery ----
namespace OAI

/-!
# Exact finite-law recovery and coefficient representations
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem pooled_expect {Ω' E : Type*} [Fintype Ω'] [AddCommMonoid E] [Module ℝ E]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (f : Ω → E) (g : Ω' → E) :
    (μ.pooled ν).expect (Sum.elim f g) = (1/2 : ℝ) • μ.expect f + (1/2 : ℝ) • ν.expect g := by
  simp only [expect, pooled, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.smul_sum, smul_smul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro ω hω <;> congr 1 <;> ring

end FiniteLaw

section LawRecovery
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end LawRecovery

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end FiniteLaw

section RepresentationGates
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

end RepresentationGates

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.TailBudget ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Signed-product recovery and the finite midpoint tail bound
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section SignedRecovery
open scoped Classical
variable {V Ω : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V] [Fintype Ω]

end SignedRecovery

section JointLawBound
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

end JointLawBound

section HeadSupport
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

theorem dual_ext_coordinates {x y : FullDual V}
    (h : ∀ v, x (unitVector v) = y (unitVector v)) : x = y := by
  apply dual_ext_test
  intro u
  simp only [dual_apply_test, h]

theorem head_eq_iff (H : Finset V) (x : FullDual V) :
    head H x = x ↔ ∀ v ∉ H, x (unitVector v) = 0 := by
  constructor
  · intro hx v hv
    rw [← hx, head_unitVector, ite_eq_right hv]
  · intro hx
    apply dual_ext_coordinates
    intro v
    rw [head_unitVector]
    by_cases hv : v ∈ H
    · simp [hv]
    · simp [hv, hx v hv]

theorem head_eq_of_subset {H K : Finset V} (hHK : H ⊆ K)
    (x : FullDual V) (hx : head H x = x) : head K x = x := by
  apply (head_eq_iff K x).mpr
  intro v hv
  exact (head_eq_iff H x).mp hx v (fun hvH => hv (hHK hvH))

end HeadSupport

theorem norm_center_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (R : ℝ) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) : ‖x‖ ≤ R := by
  have he : x = (1 / 2 : ℝ) • ((x + y) + (x - y)) := by module
  calc
    ‖x‖ = ‖(1 / 2 : ℝ) • ((x + y) + (x - y))‖ := congrArg norm he
    _ = (1 / 2 : ℝ) * ‖(x + y) + (x - y)‖ := by rw [norm_smul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖x + y‖ + ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ R := by linarith

section FiniteMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem finite_main_tail {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) (hy : head K y = y)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by
  classical
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_add] at hp
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_sq hR] using
      (norm_tail_le hH y).trans (hp.trans (by linarith : R ≤ 2 * R))
  have hc := norm_center_le x y R hp hm
  have hRp : 0 < R := (norm_pos_iff.mpr hx0).trans_le hc
  have hxK := head_eq_of_subset hHK x hx
  have hpK : head K (x + y) = x + y := by
    change headLinear K (x + y) = _
    rw [map_add, headLinear_apply, headLinear_apply, hxK, hy]
  have hmK : head K (x - y) = x - y := by
    change headLinear K (x - y) = _
    rw [map_sub, headLinear_apply, headLinear_apply, hxK, hy]
  obtain ⟨μp, Ap, hpE, hpSupp, hpMean⟩ := exists_atomic_law hK (x + y) hpK hRp hp
  obtain ⟨μm, Am, hmE, hmSupp, hmMean⟩ := exists_atomic_law hK (x - y) hmK hRp hm
  let μ := μp.pooled μm
  let A := Sum.elim Ap Am
  let σ : Option (LocalFamily K) ⊕ Option (LocalFamily K) → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hσ : ∀ ω, |σ ω| ≤ 1 := by intro ω; cases ω <;> norm_num [σ]
  have henergy : ∀ ω, (A ω).energy ≤ R ^ 2 := by
    intro ω
    cases ω with
    | inl ω => exact hpE ω
    | inr ω => exact hmE ω
  have hsupp : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K := by
    intro ω
    cases ω with
    | inl ω => exact hpSupp ω
    | inr ω => exact hmSupp ω
  have hmean : μ.expect (fun ω => (A ω).value) = x := by
    have he : (fun ω => (A ω).value) = Sum.elim (fun ω => (Ap ω).value) (fun ω => (Am ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he]
    change (μp.pooled μm).expect (Sum.elim (fun ω => (Ap ω).value) (fun ω => (Am ω).value)) = x
    rw [FiniteLaw.pooled_expect, hpMean, hmMean]
    module
  have hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y := by
    have he : (fun ω => σ ω • (A ω).value) =
        Sum.elim (fun ω => (1 : ℝ) • (Ap ω).value) (fun ω => (-1 : ℝ) • (Am ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he]
    change (μp.pooled μm).expect _ = y
    rw [FiniteLaw.pooled_expect, μp.expect_smul, μm.expect_smul, hpMean, hmMean]
    module
  obtain ⟨p, hpSupport, hpn, hpx⟩ := exists_norming_head hH x hx hx0
  let q : Test V := ‖x‖ • p
  have hqSupport : q.coeff.support ⊆ H :=
    Finsupp.support_smul.trans hpSupport
  have hqn : ‖q‖ = ‖x‖ := by
    change ‖‖x‖ • p‖ = ‖x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hpn, mul_one]
  have hxq : x (q : Primal V) = ‖x‖ ^ 2 := by
    change x ((‖x‖ • p : Test V) : Primal V) = _
    rw [UniformSpace.Completion.coe_smul, map_smul, smul_eq_mul, hpx, sq]
  exact represented_joint_bound hH μ σ hσ A hsupp x y hx hmean hsigned q hqSupport
    ‖x‖ R hqn hxq henergy

end FiniteMain

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem solution {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) (hy : head K y = y)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by
  first
    | exact OAI.SegmentLenses.finite_main_tail hH hK hHK x y hx hy R hR hp hm
    | exact OAI.SegmentLenses.finite_main_tail
    | (apply OAI.SegmentLenses.finite_main_tail <;> assumption)
    | (intros; apply OAI.SegmentLenses.finite_main_tail <;> assumption)
