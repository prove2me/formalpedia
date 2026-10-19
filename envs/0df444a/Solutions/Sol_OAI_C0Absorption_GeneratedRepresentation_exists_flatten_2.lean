-- Prove2me | solution 2 for OAI.C0Absorption.GeneratedRepresentation.exists_flatten
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:09:31.229379+00:00
-- url     : https://prove2.me/submissions/b00c4ef4-3516-4a59-9a78-0092f2616d70

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Duality.lean:L198-L250
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.GeneratedRepresentation.exists_flatten. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_VClass_lipschitz
import Theorems.Thm_OAI_C0Absorption_completedPairing_tendsto
import Theorems.Thm_OAI_C0Absorption_localG_sup

-- ---- from OAI.Analysis.C0Absorption.Localization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

noncomputable section

theorem localG_plateau {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (u : X → ℝ) (x : X) (hx : dist x q ≤ ε/2) : localG q ε u x = u q := by
  have hh : dist x q / ε ≤ 1/2 := (div_le_iff₀ hε).mpr (by linarith)
  simp [localG, chi, max_eq_left (by linarith : 2*(dist x q/ε)-1 ≤ 0)]

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

end

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Coordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

theorem dyadic_tendsto : Tendsto dyadic atTop (nhds 0) := by
  change Tendsto (fun a : ℕ => ((2 : ℝ)^a)⁻¹) atTop (nhds 0)
  simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)

theorem nearestOperationGrid_dist (I : Finset ℕ) (a : ℕ) (x : Cube I) :
    dist x (operationGridPoint I a (nearestOperationGrid I a x)) ≤ dyadic a / 16 := by
  apply (dist_pi_le_iff (div_nonneg (dyadic_pos a).le (by norm_num) : 0 ≤ dyadic a / 16)).mpr
  intro i
  have hh := nearestGrid_dist (2^(a+3)) (by positivity) (x i)
  change dist (x i) (gridPoint _ _ (nearestGridIndex _ _ (x i))) ≤ _
  refine hh.trans_eq ?_
  push_cast
  rw [dyadic, pow_add]
  norm_num
  ring

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

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem cubeValue_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.cubeValue x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  applyOperations_sup _ B.A.coe_nonneg (B.base_sup γ)

end GeneratedRepresentation

namespace TailOperation

theorem factor_abs_le (t : TailOperation) (s : C0Ball) : |t.factor s| ≤ 1 := by
  have hl := tailFactor_nonneg (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  have hu := tailFactor_le_one (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  rw [abs_le]
  unfold factor
  split <;> constructor <;> linarith

end TailOperation

theorem tailProduct_abs_le (ts : List TailOperation) (s : C0Ball) : |tailProduct ts s| ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [tailProduct_cons, abs_mul]
    exact (mul_le_mul (t.factor_abs_le s) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem eventually_append_allowed (r : GeneratedRepresentation B γ) :
    ∀ᶠ a in atTop, (∀ p ∈ r.operations, dyadic a ≤ p.scale) ∧
      (r.operations.map CylinderOperation.scale).sum+dyadic a < B.ell (B.band γ)/2 := by
  have h1 : ∀ᶠ a in atTop, ∀ p ∈ r.operations, dyadic a ≤ p.scale := by
    apply r.operations.finite_toSet.eventually_all.mpr
    intro p hp
    exact dyadic_tendsto.eventually (eventually_le_nhds p.scale_pos)
  have h2 : ∀ᶠ a in atTop, dyadic a < B.ell (B.band γ)/2-(r.operations.map CylinderOperation.scale).sum :=
    dyadic_tendsto.eventually (eventually_lt_nhds (sub_pos.mpr r.budget))
  filter_upwards [h1,h2] with a ha hb
  exact ⟨ha, by linarith⟩

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

theorem VClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ VClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h+1)
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) (by
      simpa only [sourceClasses_odd, Nat.cast_add, Nat.cast_one] using (fun f hf => VClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) hf)⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem flattenOperation_center (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    dist v (flattenOperation I a v).point ≤ dyadic a/16 := nearestOperationGrid_dist I a v

theorem flattenOperation_plateau (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ)
    (x : Cube I) (hx : dist x v < 3*dyadic a/8) :
    (flattenOperation I a v).act u x = u (flattenOperation I a v).point := by
  apply localG_plateau _ (dyadic_pos a) u x
  have hh := dist_triangle x v (flattenOperation I a v).point
  have hc := flattenOperation_center I a v
  linarith [dyadic_pos a]

theorem flattenOperation_difference (I : Finset ℕ) (a : ℕ) (v : Cube I)
    {u : Cube I → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (x : Cube I) :
    |(flattenOperation I a v).act u x-u x| ≤ dyadic a*K := by
  rw [flattenOperation_act, localG_eq, add_sub_cancel_left]
  exact localR_sup_lip _ (dyadic_pos a) u hu x

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem exists_flatten (r : GeneratedRepresentation B γ) (ts : List TailOperation)
    (h : ℕ) (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ts.length ≤ h) (hs : ∀ t ∈ ts, t.scaleIndex ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin (fun s => r'.value s*tailProduct ts s) z-
        completedPairing (sourceClasses B) c0Origin (fun s => r.value s*tailProduct ts s) z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  have he := r.eventually_append_allowed.and (dyadic_tendsto.eventually (eventually_lt_nhds hcap))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let op (n : ℕ) := flattenOperation (B.coordinates γ) (N+n) v
  have ho (n : ℕ) : ∀ p ∈ r.operations, (op n).scale ≤ p.scale := (hN (N+n) (by omega)).1.1
  have hb (n : ℕ) : (r.operations.map CylinderOperation.scale).sum+(op n).scale < B.ell (B.band γ)/2 :=
    (hN (N+n) (by omega)).1.2
  let rr (n : ℕ) := r.append (op n) (ho n) (hb n)
  let f (n : ℕ) (s : C0Ball) := (rr n).value s*tailProduct ts s
  let g (s : C0Ball) := r.value s*tailProduct ts s
  have hf (n : ℕ) : f n ∈ VClass B (h+1) := by
    refine ⟨γ,rr n,ts,?_,hj.trans (Nat.le_succ h),ht.trans (Nat.le_succ h),
      fun t hm => (hs t hm).trans (Nat.le_succ h),rfl⟩
    simpa only [rr, append, List.length_append, List.length_singleton] using Nat.add_le_add_right hr 1
  have hsc : Tendsto (fun n => dyadic (N+n)) atTop (nhds 0) :=
    dyadic_tendsto.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ N+n) tendsto_id)
  have hp (s : C0Ball) : Tendsto (fun n => f n s) atTop (nhds (g s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound (n : ℕ) : dist (f n s) (g s) ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
      simp only [f,g,Real.dist_eq,← sub_mul,abs_mul]
      have hd : |(rr n).value s-r.value s| ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
        change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)-r.cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
        rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
        exact flattenOperation_difference _ (N+n) v r.cubeValue_lipschitz _
      exact (mul_le_mul hd (tailProduct_abs_le ts s) (abs_nonneg _) (mul_nonneg (dyadic_pos _).le (NNReal.coe_nonneg _))).trans_eq (mul_one _)
    exact squeeze_zero (fun n => dist_nonneg) hbound (by simpa using hsc.mul_const ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ))
  obtain ⟨A,hA⟩ := VClass_pairing_bound B (h+1)
  have hconv := (completedPairing_tendsto (sourceClasses B) c0Origin f g A
    (fun n => hA (f n) (hf n)) hp).2 z
  have hev : ∀ᶠ n in atTop, |completedPairing (sourceClasses B) c0Origin (f n) z-
      completedPairing (sourceClasses B) c0Origin g z| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hconv) δ hδ
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨N+n,rr n,(hN (N+n) (by omega)).2,rfl,hn,?_,?_⟩
  · intro s hss
    change (rr n).cubeValue (cubeRestrict (B.coordinates γ) s) = _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact flattenOperation_plateau _ _ _ r.cubeValue _ hss
  · intro s
    change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact localG_sup _ _ _ _ r.cubeValue_sup _

end GeneratedRepresentation
end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption OAI.C0Absorption.GeneratedRepresentation
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.GeneratedRepresentation.exists_flatten := @_root_.OAI.C0Absorption.GeneratedRepresentation.exists_flatten
