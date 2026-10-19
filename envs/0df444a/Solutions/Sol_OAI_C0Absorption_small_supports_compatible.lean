-- Prove2me | solution 1 for OAI.C0Absorption.small_supports_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:24:07.378978+00:00
-- url     : https://prove2.me/submissions/e13eb89e-08bc-435a-9eb5-9c0c1c071930

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Supports.lean:L190-L265
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.small_supports_compatible. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_GeneratedRepresentation_exists_flatten
import Theorems.Thm_OAI_C0Absorption_VClass_lipschitz
import Theorems.Thm_OAI_C0Absorption_bounded_product_lipschitz
import Theorems.Thm_OAI_C0Absorption_localOp_support_bound
import Theorems.Thm_OAI_C0Absorption_nested_selection_lipschitz
import Theorems.Thm_OAI_C0Absorption_tailFactor_lipschitz

-- ---- from OAI.Analysis.C0Absorption.Coordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

theorem tailFactor_nonneg (c : ℝ) (N : ℕ) (s : C0) : 0 ≤ tailFactor c N s := by
  exact le_min zero_le_one (le_max_right _ _)

theorem tailFactor_le_one (c : ℝ) (N : ℕ) (s : C0) : tailFactor c N s ≤ 1 := min_le_left _ _

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
end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

namespace TailOperation

theorem factor_abs_le (t : TailOperation) (s : C0Ball) : |t.factor s| ≤ 1 := by
  have hl := tailFactor_nonneg (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  have hu := tailFactor_le_one (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  rw [abs_le]
  unfold factor
  split <;> constructor <;> linarith

theorem factor_lipschitz (t : TailOperation) : LipschitzWith (2^t.scaleIndex) t.factor := by
  apply LipschitzWith.of_dist_le_mul
  intro s u
  have hh := (tailFactor_lipschitz (dyadic_pos t.scaleIndex) (t.tailIndex+1)).dist_le_mul s.val u.val
  change dist (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val)
      (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) u.val) ≤
      (dyadic t.scaleIndex)⁻¹ * dist s u at hh
  simp only [dyadic, inv_inv] at hh
  simp only [NNReal.coe_pow, NNReal.coe_ofNat]
  cases ht : t.isBasic
  · simpa only [factor, dyadic, ht, Bool.false_eq_true, ↓reduceIte, dist_sub_right] using hh
  · simpa only [factor, dyadic, ht, ↓reduceIte] using hh

end TailOperation

theorem tailProduct_abs_le (ts : List TailOperation) (s : C0Ball) : |tailProduct ts s| ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [tailProduct_cons, abs_mul]
    exact (mul_le_mul (t.factor_abs_le s) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem tailProduct_lipschitz (ts : List TailOperation) :
    LipschitzWith ((ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum) (tailProduct ts) := by
  induction ts with
  | nil =>
    change LipschitzWith 0 (fun _ : C0Ball => (1 : ℝ))
    exact LipschitzWith.const 1
  | cons t ts ih =>
    have hh := bounded_product_lipschitz (A := 1) (B := 1) t.factor_lipschitz ih t.factor_abs_le (tailProduct_abs_le ts)
    convert hh using 1 <;> first | rfl | simp only [List.map_cons, List.sum_cons, one_mul, add_comm]

theorem tailProduct_lipschitz_bound (ts : List TailOperation) (h : ℕ)
    (hlen : ts.length ≤ h) (hscale : ∀ t ∈ ts, t.scaleIndex ≤ h) :
    LipschitzWith ((h : ℝ≥0)*2^h) (tailProduct ts) := by
  apply (tailProduct_lipschitz ts).weaken
  calc
    (ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum ≤
        (ts.map (fun _ => (2 : ℝ≥0)^h)).sum := List.sum_le_sum
          (fun t ht => pow_le_pow_right₀ (by norm_num) (hscale t ht))
    _ = (ts.length : ℝ≥0)*2^h := by simp
    _ ≤ (h : ℝ≥0)*2^h := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)

theorem tsupport_comp_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) {π : X → Y} (hπ : Continuous π) :
    tsupport (f ∘ π) ⊆ π ⁻¹' tsupport f := by
  apply closure_minimal
  · intro x hx; exact subset_tsupport f hx
  · exact (isClosed_tsupport f).preimage hπ

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Supports ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace RadiusLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : RadiusLocalization B)

end RadiusLocalization
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem small_supports_compatible {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (q : ℕ → Cube (B.coordinates γ)) (a b : ℕ → ℝ)
    (haPos : ∀ i, 0 < a i) (ha0 : Tendsto a atTop (nhds 0)) (hb0 : Tendsto b atTop (nhds 0))
    (hsup : ∀ i x, |(r i).cubeValue x| ≤ b i)
    (hsupp : ∀ i x, x ∈ tsupport (r i).cubeValue → dist x (q i) ≤ a i)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A+1)
          (fun s => ∑ i, ε i*F i s) := by
  obtain ⟨v,hv,ψ,hψ,hvψ⟩ := isCompact_univ.isSeqCompact.subseq_of_frequently_in
    (x := q) (Filter.Eventually.of_forall (fun _ => mem_univ _)).frequently
  have hfl (i : ℕ) := (r (ψ i)).exists_flatten (ts (ψ i)) h (hr _) hj (ht _) (ha _)
    v (m (ψ i)) (half_pos hδ) (haPos (ψ i))
  choose θ rr hcap hops hdif hflat hsupold using hfl
  have hmem (i : ℕ) : (fun s => (rr i).value s*tailProduct (ts (ψ i)) s) ∈ VClass B (h+1) := by
    refine ⟨γ,rr i,ts (ψ i),?_,hj.trans (Nat.le_succ _),(ht _).trans (Nat.le_succ _),
      fun t hm => (ha _ t hm).trans (Nat.le_succ _),rfl⟩
    rw [hops i,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (hr (ψ i)) 1
  have hnew (i : ℕ) (s : C0Ball) (hs : s ∈ tsupport (rr i).value) :
      dist (cubeRestrict (B.coordinates γ) s) (q (ψ i)) ≤ 2*a (ψ i) := by
    have he : (rr i).cubeValue = (flattenOperation (B.coordinates γ) (θ i) v).act (r (ψ i)).cubeValue := by
      simp only [GeneratedRepresentation.cubeValue,hops i,applyOperations_append,applyOperations_cons,applyOperations_nil]
    have hcube := tsupport_comp_subset (rr i).cubeValue (cubeRestrict_lipschitz _).continuous hs
    rw [he] at hcube
    have hh := localOp_support_bound true (flattenOperation (B.coordinates γ) (θ i) v).point
      (dyadic_pos (θ i)) (r (ψ i)).cubeValue (fun x => dist x (q (ψ i)))
      (LipschitzWith.dist_left _) (a (ψ i)) (hsupp (ψ i)) _ hcube
    simp only [NNReal.coe_one] at hh
    linarith [hcap i]
  let C (i : ℕ) : Set C0Ball :=
    {s | dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic (θ i)/8}
  let e (i : ℕ) := (r (ψ i)).cubeValue (flattenOperation (B.coordinates γ) (θ i) v).point
  have hC (i : ℕ) : IsOpen (C i) :=
    Metric.isOpen_ball.preimage (cubeRestrict_lipschitz _).continuous
  have hnest (i : ℕ) : ∀ᶠ j in atTop, tsupport (rr j).value ⊆ C i := by
    have hrad : Tendsto (fun j => 2*a (ψ j)+dist (q (ψ j)) v) atTop (nhds 0) := by
      simpa only [Function.comp_def,mul_zero,dist_self,zero_add] using
        ((ha0.comp hψ.tendsto_atTop).const_mul 2).add (hvψ.dist (show Tendsto (fun _ : ℕ => v) atTop (nhds v) from tendsto_const_nhds))
    have he := hrad.eventually (eventually_lt_nhds
      (show (0 : ℝ)<3*dyadic (θ i)/8 by have := dyadic_pos (θ i); positivity))
    filter_upwards [he] with j hj
    intro s hs
    exact lt_of_le_of_lt ((dist_triangle _ (q (ψ j)) _).trans (add_le_add (hnew j s hs) le_rfl)) hj
  have hesmall : Tendsto (fun i => |e i| * ((h : ℝ≥0)*2^h : ℝ≥0)) atTop (nhds 0) := by
    have he0 : Tendsto (fun i => |e i|) atTop (nhds 0) := squeeze_zero
      (fun _ => abs_nonneg _) (fun i => hsup (ψ i) _) (hb0.comp hψ.tendsto_atTop)
    simpa only [zero_mul] using he0.mul_const (((h : ℝ≥0)*2^h : ℝ≥0) : ℝ)
  obtain ⟨η,hη,hLip⟩ := nested_selection_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i => (rr i).value) (fun i => tailProduct (ts (ψ i))) C e
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) ((h : ℝ≥0)*2^h)
    (fun i => (rr i).value_lipschitz.continuous)
    (fun i => tailProduct_lipschitz_bound _ h (ht _) (ha _))
    (fun i => by simpa only [Nat.cast_add,Nat.cast_one] using VClass_lipschitz B (h+1) (hmem i)) hC (fun i s hs => hflat i s hs) hnest hesmall
  refine ⟨ψ ∘ η,hψ.comp hη,fun i s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s,
    fun i => hmem _,?_,hLip⟩
  intro i
  have hb := hdif (η i)
  have hh := hd (ψ (η i))
  have hab := abs_sub_abs_le_abs_sub
    (completedPairing (sourceClasses B) c0Origin
      (fun s => (r (ψ (η i))).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i))))
    (completedPairing (sourceClasses B) c0Origin
      (fun s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i))))
  rw [abs_sub_comm] at hab
  change δ/2 ≤ |completedPairing (sourceClasses B) c0Origin
    (fun s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i)))|
  linarith

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


theorem solution : type_of% @_root_.OAI.C0Absorption.small_supports_compatible := @_root_.OAI.C0Absorption.small_supports_compatible
