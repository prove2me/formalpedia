-- Prove2me | solution 1 for OAI.C0Absorption.high_bands_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:18:23.07274+00:00
-- url     : https://prove2.me/submissions/274f23a7-e650-4ee6-a72d-06d2e8a5c24e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Selection.lean:L211-L258
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.high_bands_compatible. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_GeneratedRepresentation_exists_flatten_T
import Theorems.Thm_OAI_C0Absorption_localOp_support_bound
import Theorems.Thm_OAI_C0Absorption_nested_selection_lipschitz

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

theorem tsupport_comp_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) {π : X → Y} (hπ : Continuous π) :
    tsupport (f ∘ π) ⊆ π ⁻¹' tsupport f := by
  apply closure_minimal
  · intro x hx; exact subset_tsupport f hx
  · exact (isClosed_tsupport f).preimage hπ

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem support_bound (r : GeneratedRepresentation B γ) {φ : Cube (B.coordinates γ) → ℝ}
    (hφ : LipschitzWith 1 φ) {b : ℝ} (hu : ∀ x ∈ tsupport (B.base γ), φ x ≤ b) :
    ∀ s ∈ tsupport r.value,
      φ (cubeRestrict (B.coordinates γ) s) ≤ b+(r.operations.map CylinderOperation.scale).sum := by
  intro s hs
  have hm := tsupport_comp_subset r.cubeValue (cubeRestrict_lipschitz (B.coordinates γ)).continuous hs
  exact applyOperations_support_bound r.operations (B.base γ) hφ hu _ hm

end GeneratedRepresentation

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Selection ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TagLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)

theorem representation_support {γ : Γ} (r : GeneratedRepresentation B γ)
    (k : ℕ) (hk : k < B.band γ) (s : C0Ball) (hs : s ∈ tsupport r.value) :
    dist (s.val k) (loc.tag γ k).val ≤ 2*dyadic (B.band γ)+B.ell (B.band γ)/2 := by
  let l : B.coordinates γ := ⟨k,loc.contains_prefix γ (Finset.mem_range.mpr hk)⟩
  let φ : Cube (B.coordinates γ) → ℝ := fun x => dist (x l) (loc.tag γ k)
  have hφ : LipschitzWith 1 φ := by
    simpa only [φ,Function.comp_def,one_mul] using (LipschitzWith.dist_left (loc.tag γ k)).comp (LipschitzWith.eval l)
  have hp := r.support_bound hφ (loc.base_support γ l hk) s hs
  exact hp.trans (add_le_add le_rfl r.budget.le)

theorem projected_concentration (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (hj : Tendsto (fun i => B.band (γ i)) atTop atTop)
    (v : ℕ → Icc (-1 : ℝ) 1) (hv : Tendsto (fun i => loc.tag (γ i)) atTop (nhds v))
    (I : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ s ∈ tsupport (r i).value,
      dist (cubeRestrict I s) (fun k : I => v k.val) < ε := by
  have ha : Tendsto (fun i => 2*dyadic (B.band (γ i))+B.ell (B.band (γ i))/2) atTop (nhds 0) := by
    simpa only [Function.comp_def,mul_zero,zero_div,zero_add] using
      ((dyadic_tendsto.comp hj).const_mul 2).add ((loc.ell_tendsto.comp hj).div_const 2)
  have he := ha.eventually (eventually_lt_nhds (half_pos hε))
  have hall : ∀ᶠ i in atTop, ∀ k : I, k.val < B.band (γ i) ∧
      dist (loc.tag (γ i) k.val) (v k.val) < ε/2 := by
    apply Filter.eventually_all.mpr
    intro k
    exact (hj.eventually (eventually_gt_atTop k.val)).and
      ((Metric.tendsto_nhds.mp (tendsto_pi_nhds.mp hv k.val)) (ε/2) (half_pos hε))
  filter_upwards [he,hall] with i hi htag
  intro s hs
  apply (dist_pi_lt_iff hε).mpr
  intro k
  have hb := loc.representation_support (r i) k.val (htag k).1 s hs
  have hc := (htag k).2
  have hd := dist_triangle (cubeRestrict I s k) (loc.tag (γ i) k.val) (v k.val)
  change dist (s.val k.val) (v k.val).val < ε
  change dist (s.val k.val) (v k.val).val ≤
    dist (s.val k.val) (loc.tag (γ i) k.val).val + dist (loc.tag (γ i) k.val) (v k.val) at hd
  linarith

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem high_bands_compatible {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)
    (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i)) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h)
    (hj : Tendsto (fun i => B.band (γ i)) atTop atTop)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (r i).value (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ TClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+1) (fun s => ∑ i, ε i*F i s) := by
  obtain ⟨v,hv,ψ,hψ,hvψ⟩ := isCompact_univ.isSeqCompact.subseq_of_frequently_in
    (x := fun i => loc.tag (γ i)) (Filter.Eventually.of_forall (fun _ => mem_univ _)).frequently
  have hfl (i : ℕ) := (r (ψ i)).exists_flatten_T h (hr (ψ i))
    (fun k => v k.val) (m (ψ i)) (half_pos hδ) (show (0 : ℝ)<1 by norm_num)
  choose a rr hcap hops hdif hflat hsup using hfl
  have hmem (i : ℕ) : (rr i).value ∈ TClass B (h+1) := by
    refine ⟨γ (ψ i),rr i,?_,rfl⟩
    rw [hops i,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (hr (ψ i)) 1
  let C (i : ℕ) : Set C0Ball :=
    {s | dist (cubeRestrict (B.coordinates (γ (ψ i))) s)
      (fun k => v k.val) < 3*dyadic (a i)/8}
  let e (i : ℕ) := (r (ψ i)).cubeValue
    (flattenOperation (B.coordinates (γ (ψ i))) (a i) (fun k => v k.val)).point
  have hC (i : ℕ) : IsOpen (C i) :=
    Metric.isOpen_ball.preimage (cubeRestrict_lipschitz _).continuous
  have hnest (i : ℕ) : ∀ᶠ j in atTop, tsupport (rr j).value ⊆ C i := by
    have hp := loc.projected_concentration (γ ∘ ψ) rr (hj.comp hψ.tendsto_atTop) v hvψ
      (B.coordinates (γ (ψ i))) (show 0 < 3*dyadic (a i)/8 by have := dyadic_pos (a i); positivity)
    exact hp
  obtain ⟨η,hη,hLip⟩ := nested_selection_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i => (rr i).value) (fun _ _ => 1) C e (4^(h+1)*B.L0) 0
    (fun i => (rr i).value_lipschitz.continuous) (fun _ => LipschitzWith.const 1)
    (fun i => by simpa only [mul_one] using TClass_lipschitz B (h+1) (hmem i))
    hC (fun i s hs => hflat i s hs) hnest (by simp only [NNReal.coe_zero,mul_zero]; exact tendsto_const_nhds)
  refine ⟨ψ ∘ η,hψ.comp hη,fun i => (rr (η i)).value,fun i => hmem _,?_,?_⟩
  · intro i
    have hb := hdif (η i)
    have ha := hd (ψ (η i))
    have hab := abs_sub_abs_le_abs_sub
      (completedPairing (sourceClasses B) c0Origin (r (ψ (η i))).value (m (ψ (η i))))
      (completedPairing (sourceClasses B) c0Origin (rr (η i)).value (m (ψ (η i))))
    rw [abs_sub_comm] at hab
    change δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (rr (η i)).value (m (ψ (η i)))|
    linarith
  · intro n ε hε
    simpa only [mul_one] using hLip n ε hε

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


theorem solution : type_of% @_root_.OAI.C0Absorption.high_bands_compatible := @_root_.OAI.C0Absorption.high_bands_compatible
