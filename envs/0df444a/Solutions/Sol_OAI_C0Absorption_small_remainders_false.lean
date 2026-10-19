-- Prove2me | solution 1 for OAI.C0Absorption.small_remainders_false
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:27:40.936091+00:00
-- url     : https://prove2.me/submissions/8219c93c-dcae-41d2-83f6-e362e8bfbeab

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Operations.lean:L223-L268
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.small_remainders_false. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Theorems.Thm_OAI_C0Absorption_compatible_detectors_false
import Theorems.Thm_OAI_C0Absorption_localG_sup
import Theorems.Thm_OAI_C0Absorption_localOp_support_bound
import Theorems.Thm_OAI_C0Absorption_small_supports_compatible

-- ---- from OAI.Analysis.C0Absorption.Localization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

noncomputable section

theorem localR_sup_lip {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) (x : X) :
    |localR q ε u x| ≤ ε * L := by
  rw [localR_eq, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _)]
  by_cases hx : cutoff q ε x = 0
  · rw [hx, zero_mul]; positivity
  have hd := (dist_lt_of_cutoff_ne_zero q hε x hx).le
  have hb : |u q-u x| ≤ ε * L := by
    calc
      |u q-u x| ≤ L * dist q x := hu.dist_le_mul q x
      _ ≤ L * ε := mul_le_mul_of_nonneg_left (by rwa [dist_comm]) L.coe_nonneg
      _ = ε*L := mul_comm _ _
  exact (mul_le_mul_of_nonneg_right (cutoff_le_one q ε x) (abs_nonneg _)).trans (by simpa using hb)

theorem localR_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localR q ε u x| ≤ 2*A := by
  calc
    |localR q ε u x| = |localG q ε u x-u x| := rfl
    _ ≤ |localG q ε u x|+|u x| := abs_sub _ _
    _ ≤ A+A := add_le_add (localG_sup q ε u A hu x) (hu x)
    _ = 2*A := by ring

theorem localR_support_ball {X : Type*} [PseudoMetricSpace X] (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) :
    tsupport (localR q ε u) ⊆ Metric.closedBall q ε := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have ha : cutoff q ε x ≠ 0 := by
    intro ha
    have hx' : localR q ε u x ≠ 0 := hx
    simp [localR_eq, ha] at hx'
  exact (dist_lt_of_cutoff_ne_zero q hε x ha).le

end

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Tests ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace CylinderOperation
variable {I : Finset ℕ}
theorem act_sup (r : CylinderOperation I) {A : ℝ} (hA : 0 ≤ A)
    {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) : ∀ x, |r.act u x| ≤ 2*A := by
  intro x
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact localR_sup r.point r.scale u A hu x
  · exact (localG_sup r.point r.scale u A hu x).trans (by linarith)

end CylinderOperation

theorem applyOperations_sup {I : Finset ℕ} (ops : List (CylinderOperation I))
    {A : ℝ} (hA : 0 ≤ A) {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) :
    ∀ x, |applyOperations ops u x| ≤ 2^ops.length*A := by
  induction ops generalizing A u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (by positivity : 0 ≤ 2*A) (r.act_sup hA hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh

theorem applyOperations_support_bound {I : Finset ℕ} (ops : List (CylinderOperation I))
    (u : Cube I → ℝ) {φ : Cube I → ℝ} (hφ : LipschitzWith 1 φ) {b : ℝ}
    (hu : ∀ x ∈ tsupport u, φ x ≤ b) :
    ∀ x ∈ tsupport (applyOperations ops u), φ x ≤ b+(ops.map CylinderOperation.scale).sum := by
  induction ops generalizing u b with
  | nil => simpa using hu
  | cons r rs ih =>
    have hnew : ∀ x ∈ tsupport (r.act u), φ x ≤ b+r.scale := by
      simpa only [CylinderOperation.act, NNReal.coe_one, mul_one] using localOp_support_bound r.isG r.point r.scale_pos u φ hφ b hu
    have hh := ih (r.act u) hnew
    simpa only [List.map_cons, List.sum_cons, applyOperations_cons, add_assoc] using hh

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

namespace TailOperation

end TailOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Duality ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section ClassDuality
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end ClassDuality

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_mono {h k : ℕ} (hk : h ≤ k) : VClass B h ⊆ VClass B k := by
  rintro f ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩
  exact ⟨γ,r,ts,hr.trans hk,hj.trans hk,ht.trans hk,fun t hm => (hs t hm).trans hk,rfl⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation
end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Operations ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace SignedBound
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ → X} {M : ℝ} (hm : SignedBound m M)

include hm

theorem subsequence {φ : ℕ → ℕ} (hφ : Function.Injective φ) : SignedBound (m ∘ φ) M :=
  fun n ι hι ε => hm n (φ ∘ ι) (hφ.comp hι) ε

end SignedBound

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_compatible_false (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ VClass B h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  apply compatible_detectors_false (sourceClasses B) c0Origin m M hm F (2*h+1) K _ hLip hδ hd
  intro i
  simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) (hF i)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace CylinderOperation
variable {I : Finset ℕ}

end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem small_remainders_false {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (op : ℕ → CylinderOperation (B.coordinates γ))
    (hsmall : Tendsto (fun i => (op i).scale) atTop (nhds 0))
    (p : Cube (B.coordinates γ) → ℝ) (K : ℝ≥0) (hp : LipschitzWith K p)
    (suf : ℕ → List (CylinderOperation (B.coordinates γ)))
    (hlen : ∀ i, (suf i).length ≤ h)
    (horder : ∀ i t, t ∈ suf i → t.scale ≤ (op i).scale)
    (heq : ∀ i, (r i).cubeValue = applyOperations (suf i) ((op i).remainder.act p))
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  let a (i : ℕ) : ℝ := (h+1)*(op i).scale
  let b (i : ℕ) : ℝ := 2^h*K*(op i).scale
  have haPos (i : ℕ) : 0 < a i := by
    dsimp [a]; have := (op i).scale_pos; positivity
  have ha0 : Tendsto a atTop (nhds 0) := by simpa only [a,mul_zero] using hsmall.const_mul (h+1 : ℝ)
  have hb0 : Tendsto b atTop (nhds 0) := by simpa only [b,mul_zero] using hsmall.const_mul (2^h*(K : ℝ))
  have hsup (i : ℕ) (x : Cube (B.coordinates γ)) : |(r i).cubeValue x| ≤ b i := by
    rw [heq i]
    have hh := applyOperations_sup (suf i) (mul_nonneg (op i).scale_pos.le K.coe_nonneg)
      (fun x => localR_sup_lip (op i).point (op i).scale_pos p hp x) x
    rw [CylinderOperation.remainder_act]
    calc
      _ ≤ 2^(suf i).length*((op i).scale*K) := hh
      _ ≤ 2^h*((op i).scale*K) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (hlen i)) (mul_nonneg (op i).scale_pos.le K.coe_nonneg)
      _ = b i := by dsimp [b]; ring
  have hsupp (i : ℕ) (x : Cube (B.coordinates γ)) (hx : x ∈ tsupport (r i).cubeValue) :
      dist x (op i).point ≤ a i := by
    rw [heq i,CylinderOperation.remainder_act] at hx
    have hh := applyOperations_support_bound (suf i) (localR (op i).point (op i).scale p)
      (LipschitzWith.dist_left (op i).point) (fun x hx => localR_support_ball (op i).point (op i).scale_pos p hx) x hx
    have hs : ((suf i).map CylinderOperation.scale).sum ≤ (h : ℝ)*(op i).scale := by
      calc
        _ ≤ ((suf i).map (fun _ => (op i).scale)).sum := List.sum_le_sum (fun t ht => horder i t ht)
        _ = ((suf i).length : ℝ)*(op i).scale := by simp
        _ ≤ (h : ℝ)*(op i).scale := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen i) (op i).scale_pos.le
    dsimp [a]
    linarith
  obtain ⟨φ,hφ,F,hF,hdF,hLip⟩ := small_supports_compatible r ts h hr hj ht ha
    (fun i => (op i).point) a b haPos ha0 hb0 hsup hsupp m hδ hd
  exact VClass_compatible_false (m ∘ φ) M (hm.subsequence hφ.injective) F (h+1) _ hF hLip (half_pos hδ) hdF

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TailOperation
end TailOperation

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.small_remainders_false := @_root_.OAI.C0Absorption.small_remainders_false
