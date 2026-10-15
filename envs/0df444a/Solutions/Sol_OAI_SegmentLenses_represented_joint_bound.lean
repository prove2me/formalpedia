-- Prove2me | solution 1 for OAI.SegmentLenses.represented_joint_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:45:21.824217+00:00
-- url     : https://prove2.me/submissions/171d29e2-304e-4c26-954b-736a0d011d70

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/TailBudget.lean:L84-L173
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.represented_joint_bound. The node keeps its source
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
import Theorems.Thm_OAI_SegmentLenses_FiniteLaw_sq_mean_le
import Theorems.Thm_OAI_SegmentLenses_Representation_gate_energy_le
import Theorems.Thm_OAI_SegmentLenses_Representation_norm_le
import Theorems.Thm_OAI_SegmentLenses_SegmentFamily_gateTail_cone
import Theorems.Thm_OAI_SegmentLenses_SegmentFamily_gateTail_segment
import Theorems.Thm_OAI_SegmentLenses_SegmentFamily_tail_replacement
import Theorems.Thm_OAI_SegmentLenses_cone_reconstruction
import Theorems.Thm_OAI_SegmentLenses_opposite_crossing

-- ---- from OAI.Analysis.SegmentLenses.FiniteLaws ----
namespace OAI

/-!
# Finite probability laws and joint square-root budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

theorem joint_sqrt_bound {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ) :
    Real.sqrt η + Real.sqrt (η + 2 * θ) ≤ 2 * Real.sqrt (η + θ) := by
  have hηθ : 0 ≤ η + θ := by positivity
  have hη2θ : 0 ≤ η + 2 * θ := by positivity
  have h0 := Real.sqrt_nonneg η
  have h1 := Real.sqrt_nonneg (η + 2 * θ)
  have h2 := Real.sqrt_nonneg (η + θ)
  have hs0 := Real.sq_sqrt hη
  have hs1 := Real.sq_sqrt hη2θ
  have hs2 := Real.sq_sqrt hηθ
  have hprod : Real.sqrt η * Real.sqrt (η + 2 * θ) ≤ η + θ := by
    nlinarith [sq_nonneg (Real.sqrt (η + 2 * θ) - Real.sqrt η)]
  nlinarith

theorem joint_budget_tail {η θ R r t : ℝ}
    (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hbudget : η + θ ≤ R ^ 2 - r ^ 2)
    (htail : t ≤ Real.sqrt η + Real.sqrt (η + 2 * θ)) :
    t ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
  calc
    t ≤ Real.sqrt η + Real.sqrt (η + 2 * θ) := htail
    _ ≤ 2 * Real.sqrt (η + θ) := joint_sqrt_bound hη hθ
    _ ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
      gcongr

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem mean_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.mean f := Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω)

theorem mean_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.mean f ≤ μ.mean g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)

end FiniteLaw

end SegmentLenses

end

end OAI

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

theorem norm_expect_le (μ : FiniteLaw Ω) {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Ω → E) : ‖μ.expect f‖ ≤ μ.mean (fun ω => ‖f ω‖) := by
  calc
    ‖μ.expect f‖ ≤ ∑ ω, ‖μ.weight ω • f ω‖ := norm_sum_le _ _
    _ = μ.mean (fun ω => ‖f ω‖) := by
      simp only [mean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg _)]

theorem mean_sqrt_le (μ : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    μ.mean (fun ω => Real.sqrt (f ω)) ≤ Real.sqrt (μ.mean f) := by
  have h := μ.sq_mean_le (fun ω => Real.sqrt (f ω))
  simp only [Real.sq_sqrt (hf _)] at h
  have hs := Real.sq_sqrt (μ.mean_nonneg hf)
  nlinarith [Real.sqrt_nonneg (μ.mean f)]

theorem product_mean {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω')
    (f : Ω × Ω' → ℝ) :
    (μ.product ν).mean f = μ.mean (fun ω => ν.mean (fun ω' => f (ω, ω'))) := by
  simp only [mean, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem product_mul {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω')
    (f : Ω → ℝ) (g : Ω' → ℝ) :
    (μ.product ν).mean (fun ω => f ω.1 * g ω.2) = μ.mean f * ν.mean g := by
  rw [product_mean]
  simp only [mean_mul]
  simp only [mean, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

end FiniteLaw

section LawRecovery
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end LawRecovery

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem absolute_mass_identity (μ : FiniteLaw Ω) (b : Ω → Γ → ℝ) :
    (∑ g, μ.mean (fun ω => |b ω g|) ^ 2) -
      (∑ g, μ.mean (fun ω => b ω g) ^ 2) =
    (μ.product μ).mean (fun ω => ∑ g, (|b ω.1 g * b ω.2 g| - b ω.1 g * b ω.2 g)) := by
  have ha : ∀ g, (μ.product μ).mean (fun ω => |b ω.1 g| * |b ω.2 g|) =
      μ.mean (fun ω => |b ω g|) ^ 2 := fun g => by
    rw [μ.product_mul μ (fun ω => |b ω g|) (fun ω => |b ω g|), sq]
  have hb : ∀ g, (μ.product μ).mean (fun ω => b ω.1 g * b ω.2 g) =
      μ.mean (fun ω => b ω g) ^ 2 := fun g => by
    rw [μ.product_mul μ (fun ω => b ω g) (fun ω => b ω g), sq]
  simp only [mean_sum, mean_sub, abs_mul, ha, hb, Finset.sum_sub_distrib]

theorem absolute_mass_bound (μ : FiniteLaw Ω) (b : Ω → Γ → ℝ) (L : Ω → ℝ)
    (h : ∀ ω ω', (∑ g, (|b ω g * b ω' g| - b ω g * b ω' g)) ≤ L ω + L ω') :
    (∑ g, μ.mean (fun ω => |b ω g|) ^ 2) ≤
      (∑ g, μ.mean (fun ω => b ω g) ^ 2) + 2 * μ.mean L := by
  have hm := (μ.product μ).mean_mono (fun ω => h ω.1 ω.2)
  rw [← absolute_mass_identity] at hm
  have he : (μ.product μ).mean (fun ω => L ω.1 + L ω.2) = 2 * μ.mean L := by
    rw [product_mean]
    simp only [mean_add, mean_const]
    ring
  rw [he] at hm
  linarith

theorem signed_mass_bound (μ : FiniteLaw Ω) (b W : Ω → Γ → ℝ) (V : Ω → ℝ)
    (hzero : ∀ g, μ.mean (fun ω => b ω g + W ω g) = 0)
    (hW : ∀ ω, (∑ g, W ω g ^ 2) ≤ V ω) :
    (∑ g, μ.mean (fun ω => b ω g) ^ 2) ≤ μ.mean V := by
  calc
    (∑ g, μ.mean (fun ω => b ω g) ^ 2) = ∑ g, μ.mean (fun ω => W ω g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g hg
      have h := hzero g
      rw [mean_add] at h
      have he : μ.mean (fun ω => b ω g) = - μ.mean (fun ω => W ω g) := by linarith only [h]
      rw [he, neg_sq]
    _ ≤ ∑ g, μ.mean (fun ω => W ω g ^ 2) :=
      Finset.sum_le_sum (fun g _ => μ.sq_mean_le (fun ω => W ω g))
    _ = μ.mean (fun ω => ∑ g, W ω g ^ 2) := (μ.mean_sum _).symm
    _ ≤ μ.mean V := μ.mean_mono hW

theorem joint_mass_bound (μ : FiniteLaw Ω) (b W : Ω → Γ → ℝ) (V L : Ω → ℝ)
    (hzero : ∀ g, μ.mean (fun ω => b ω g + W ω g) = 0)
    (hW : ∀ ω, (∑ g, W ω g ^ 2) ≤ V ω)
    (hc : ∀ ω ω', (∑ g, (|b ω g * b ω' g| - b ω g * b ω' g)) ≤ L ω + L ω') :
    (∑ g, μ.mean (fun ω => |b ω g|) ^ 2) ≤ μ.mean V + 2 * μ.mean L :=
  (μ.absolute_mass_bound b L hc).trans (add_le_add (μ.signed_mass_bound b W V hzero hW) le_rfl)

end FiniteLaw

section RepresentationGates
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

end RepresentationGates

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.GateRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Gate coefficients, cone recovery, and energy budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section ProjectionAlgebra
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

namespace SegmentFamily

end SegmentFamily

namespace Representation

theorem error_slack_identity (A : Representation V) (p : V →₀ ℝ) (r : ℝ) :
    (A.error p).energy + (r ^ 2 - A.family.seminorm p ^ 2) =
      A.energy - 2 * (∑ S : A.family.sets, A.coeff S * ∑ v ∈ S.val, p v) + r ^ 2 := by
  rw [error_energy, SegmentFamily.seminorm_sq]
  unfold energy
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem energy_nonneg (A : Representation V) : 0 ≤ A.energy := by
  have _ := decidableEqV
  exact
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end Representation
end ProjectionAlgebra

section GateTails
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace SegmentFamily

end SegmentFamily
end GateTails

section GateRecovery
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

namespace SegmentFamily

end SegmentFamily
end GateRecovery

section ScaledLaws
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace Representation

end Representation

end ScaledLaws

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

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

theorem tail_expect_smul (H : Finset V) (μ : FiniteLaw Ω) (σ : Ω → ℝ) (f : Ω → FullDual V) :
    tail H (μ.expect (fun ω => σ ω • f ω)) = μ.expect (fun ω => σ ω • tail H (f ω)) := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  simpa only [map_smul, tailLinear_apply] using
    (μ.expect_map (tailLinear H) (fun ω => σ ω • f ω)).symm

theorem norm_signed_tail_expect_le {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1) (f : Ω → FullDual V) :
    ‖tail H (μ.expect (fun ω => σ ω • f ω))‖ ≤ μ.mean (fun ω => ‖f ω‖) := by
  rw [tail_expect_smul]
  apply (μ.norm_expect_le _).trans
  apply μ.mean_mono
  intro ω
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hσ ω)).trans (norm_tail_le hH (f ω))

theorem signed_replacement_recovery {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (A : Ω → Representation V)
    (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement p).value)) =
      ∑ g : K.filter (Gate H), μ.expect (fun ω =>
        (σ ω * (A ω).family.boundary p g.val) • segmentFunctional ((A ω).family.gateTail H g.val)) := by
  rw [tail_expect_smul]
  calc
    μ.expect (fun ω => σ ω • tail H ((A ω).family.replacement p).value) =
        μ.expect (fun ω => ∑ g : K.filter (Gate H),
          (σ ω * (A ω).family.boundary p g.val) • segmentFunctional ((A ω).family.gateTail H g.val)) := by
      congr 1
      funext ω
      rw [(A ω).family.tail_replacement hH p hp (hK ω)]
      simp only [Finset.smul_sum, smul_smul]
    _ = _ := μ.expect_sum _

theorem norm_signed_replacement_le {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1) (A : Ω → Representation V)
    (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    ‖tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement p).value))‖ ≤
      Real.sqrt (∑ g : K.filter (Gate H), μ.mean (fun ω => |(A ω).family.boundary p g.val|) ^ 2) := by
  rw [signed_replacement_recovery hH μ σ A hK p hp]
  apply cone_reconstruction (K.filter (Gate H)) (fun g hg => (Finset.mem_filter.mp hg).2) μ σ hσ
  · intro g ω
    exact (A ω).family.gateTail_segment hH g.val
  · intro g ω v hv
    exact (A ω).family.gateTail_cone (Finset.mem_filter.mp g.property).2 hv

end SignedRecovery

section JointLawBound
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

theorem represented_joint_bound {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (A : Ω → Representation V) (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (x y : FullDual V) (hx : head H x = x)
    (hmean : μ.expect (fun ω => (A ω).value) = x)
    (hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y)
    (q : Test V) (hq : q.coeff.support ⊆ H) (r R : ℝ)
    (hqr : ‖q‖ = r) (hxq : x (q : Primal V) = r ^ 2)
    (hR : ∀ ω, (A ω).energy ≤ R ^ 2) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
  classical
  let G := K.filter (Gate H)
  have hG : ∀ g ∈ G, Gate H g := fun g hg => (Finset.mem_filter.mp hg).2
  let err := fun ω => (A ω).error q.coeff
  let slack := fun ω => r ^ 2 - (A ω).family.seminorm q.coeff ^ 2
  let η := μ.mean (fun ω => (err ω).energy)
  let θ := μ.mean slack
  have hnormq : segmentSeminorm V q.coeff = r := hqr
  have herr : ∀ ω, 0 ≤ (err ω).energy := fun ω => (err ω).energy_nonneg
  have hslack : ∀ ω, 0 ≤ slack ω := by
    intro ω
    have hf := le_segmentSeminorm (A ω).family q.coeff
    rw [hnormq] at hf
    have hn := apply_nonneg ((A ω).family.seminorm) q.coeff
    dsimp [slack]
    nlinarith
  have hη : 0 ≤ η := μ.mean_nonneg herr
  have hθ : 0 ≤ θ := μ.mean_nonneg hslack
  have hpair : μ.mean (fun ω => ∑ S : (A ω).family.sets,
      (A ω).coeff S * (∑ v ∈ S.val, q.coeff v)) = r ^ 2 := by
    simp_rw [← Representation.apply_test]
    rw [← μ.expect_apply (fun ω => (A ω).value) (q : Primal V), hmean, hxq]
  have hidentity : η + θ = μ.mean (fun ω => (A ω).energy) - r ^ 2 := by
    change μ.mean (fun ω => (err ω).energy) + μ.mean slack = _
    rw [← μ.mean_add]
    have he : (fun ω => (err ω).energy + slack ω) = fun ω =>
        (A ω).energy - 2 * (∑ S : (A ω).family.sets, (A ω).coeff S * ∑ v ∈ S.val, q.coeff v) + r ^ 2 := by
      funext ω
      exact (A ω).error_slack_identity q.coeff r
    rw [he, μ.mean_add, μ.mean_sub, μ.mean_mul, μ.mean_const, hpair]
    ring
  have hbudget : η + θ ≤ R ^ 2 - r ^ 2 := by
    rw [hidentity]
    apply sub_le_sub_right
    exact (μ.mean_mono hR).trans_eq (μ.mean_const (R ^ 2))
  let b : Ω → G → ℝ := fun ω g => (A ω).family.boundary q.coeff g.val
  let W : Ω → G → ℝ := fun ω g => (err ω).value (unitVector g.val)
  have hzero : ∀ g, μ.mean (fun ω => b ω g + W ω g) = 0 := by
    intro g
    have he : (fun ω => b ω g + W ω g) = fun ω => (A ω).value (unitVector g.val) := by
      funext ω
      dsimp [b, W, err]
      rw [Representation.error_value, _root_.sub_apply, SegmentFamily.replacement_gate]
      ring
    rw [he, ← μ.expect_apply (fun ω => (A ω).value) (unitVector g.val), hmean]
    rw [← hx, head_unitVector, ite_eq_right (hG _ g.property).1]
  have hW : ∀ ω, (∑ g : G, W ω g ^ 2) ≤ (err ω).energy :=
    fun ω => (err ω).gate_energy_le G hG
  have hcross : ∀ ω ω', (∑ g : G, (|b ω g * b ω' g| - b ω g * b ω' g)) ≤
      slack ω + slack ω' := by
    intro ω ω'
    simpa only [b, slack, hnormq] using
      opposite_crossing (A ω).family (A ω').family hH q.coeff hq G hG
  have hmass : (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) ≤ η + 2 * θ :=
    μ.joint_mass_bound b W (fun ω => (err ω).energy) slack hzero hW hcross
  have he_bound : ‖tail H (μ.expect (fun ω => σ ω • (err ω).value))‖ ≤ Real.sqrt η := by
    calc
      ‖tail H (μ.expect (fun ω => σ ω • (err ω).value))‖ ≤
          μ.mean (fun ω => ‖(err ω).value‖) := norm_signed_tail_expect_le hH μ σ hσ _
      _ ≤ μ.mean (fun ω => Real.sqrt (err ω).energy) := μ.mean_mono (fun ω => (err ω).norm_le)
      _ ≤ Real.sqrt η := μ.mean_sqrt_le _ herr
  have hr_bound : ‖tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement q.coeff).value))‖ ≤
      Real.sqrt (η + 2 * θ) := by
    exact (norm_signed_replacement_le hH μ σ hσ A hK q.coeff hq).trans
      (Real.sqrt_le_sqrt hmass)
  have hy : y = μ.expect (fun ω => σ ω • (err ω).value) +
      μ.expect (fun ω => σ ω • ((A ω).family.replacement q.coeff).value) := by
    rw [← hsigned, ← μ.expect_add]
    congr 1
    funext ω
    rw [← smul_add]
    dsimp [err]
    rw [Representation.error_value, sub_add_cancel]
  have hytail : tail H y = tail H (μ.expect (fun ω => σ ω • (err ω).value)) +
      tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement q.coeff).value)) := by
    rw [hy]
    exact (tailLinear H).map_add _ _
  apply joint_budget_tail hη hθ hbudget
  rw [hytail]
  exact (norm_add_le _ _).trans (add_le_add he_bound hr_bound)

end JointLawBound

section HeadSupport
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

end HeadSupport

section FiniteMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end FiniteMain

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

theorem solution {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (A : Ω → Representation V) (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (x y : FullDual V) (hx : head H x = x)
    (hmean : μ.expect (fun ω => (A ω).value) = x)
    (hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y)
    (q : Test V) (hq : q.coeff.support ⊆ H) (r R : ℝ)
    (hqr : ‖q‖ = r) (hxq : x (q : Primal V) = r ^ 2)
    (hR : ∀ ω, (A ω).energy ≤ R ^ 2) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
  first
    | exact OAI.SegmentLenses.represented_joint_bound hH μ σ hσ A hK x y hx hmean hsigned q hq r R hqr hxq hR
    | exact OAI.SegmentLenses.represented_joint_bound
    | (apply OAI.SegmentLenses.represented_joint_bound <;> assumption)
    | (intros; apply OAI.SegmentLenses.represented_joint_bound <;> assumption)
