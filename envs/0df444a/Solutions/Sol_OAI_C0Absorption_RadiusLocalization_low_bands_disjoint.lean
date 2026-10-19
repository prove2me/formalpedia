-- Prove2me | solution 1 for OAI.C0Absorption.RadiusLocalization.low_bands_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:22:33.138273+00:00
-- url     : https://prove2.me/submissions/557b1cb8-703e-4ef8-aad6-18bd963087b3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Supports.lean:L148-L179
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.RadiusLocalization.low_bands_disjoint. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_localOp_support_bound
import Theorems.Thm_OAI_C0Absorption_tail_separation

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

theorem tsupport_product_subset_left {X : Type*} [TopologicalSpace X] (f g : X → ℝ) :
    tsupport (fun x => f x*g x) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  exact subset_tsupport f (left_ne_zero_of_mul (show f x*g x ≠ 0 from hx))

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

theorem choose_mono_sequence {P : ℕ → ℕ → Prop} (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, P i (φ i) := by
  have he (i j : ℕ) : ∃ k, j<k ∧ P i k := ((eventually_gt_atTop j).and (hP i)).exists
  choose next hn using he
  let φ : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun n prev => next (n+1) prev) n
  have hφs (n : ℕ) : φ (n+1) = next (n+1) (φ n) := rfl
  refine ⟨φ,strictMono_nat_of_lt_succ (fun n => ?_),?_⟩
  · rw [hφs]; exact (hn (n+1) (φ n)).1
  · intro i
    cases i with
    | zero => exact (hn 0 0).2
    | succ i => exact (hn (i+1) (φ i)).2

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

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

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

theorem tau_cubeExtend_restrict_le (I : Finset ℕ) (N : ℕ) (s : C0Ball) :
    tau N (cubeExtend I (cubeRestrict I s)).val ≤ tau N s.val := by
  classical
  apply c0_norm_le _ (tau_nonneg _ _)
  intro k
  rw [coordinateTail_apply]
  by_cases hk : N < k
  · simp only [hk, ↓reduceIte]
    change |extendFinite I (fun i => (cubeRestrict I s i).val) k| ≤ _
    rw [extendFinite_apply]
    split_ifs with hi
    · have hb := c0_norm_apply_le (coordinateTail N s.val) k
      simpa only [coordinateTail_apply,hk,↓reduceIte,tau,cubeRestrict] using hb
    · simpa using tau_nonneg N s.val
  · simpa only [hk,↓reduceIte,abs_zero] using tau_nonneg N s.val

namespace RadiusLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : RadiusLocalization B)

theorem representation_tail_lower {γ : Γ} (r : GeneratedRepresentation B γ)
    (ht : ¬loc.terminal γ) (N : ℕ) (hN : N < loc.firstCoordinate γ)
    (s : C0Ball) (hs : s ∈ tsupport r.value) :
    B.ell (B.band γ)/2 ≤ tau N s.val := by
  let φ : Cube (B.coordinates γ) → ℝ := fun x => -tau N (cubeExtend (B.coordinates γ) x).val
  have hφ : LipschitzWith 1 φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [φ,dist_neg_neg,NNReal.coe_one,one_mul]
    calc
      _ ≤ dist (cubeExtend (B.coordinates γ) x).val (cubeExtend (B.coordinates γ) y).val :=
        by simpa only [NNReal.coe_one,one_mul] using (tau_lipschitz N).dist_le_mul _ _
      _ ≤ dist x y := by
        simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq] using (cubeExtend_lipschitz (B.coordinates γ)).dist_le_mul x y
  have hb : ∀ x ∈ tsupport (B.base γ), φ x ≤ -B.ell (B.band γ) := by
    intro x hx
    exact neg_le_neg (loc.base_radius γ ht N hN x hx)
  have hh := r.support_bound hφ hb s hs
  have htau := tau_cubeExtend_restrict_le (B.coordinates γ) N s
  have hbudget := r.budget
  dsimp only [φ] at hh
  linarith

include loc in

theorem low_bands_disjoint (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (ts : ℕ → List TailOperation) (h j : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : ∀ i, B.band (γ i)=j) (hjh : j ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (hγ : Function.Injective γ) (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      Pairwise (fun i k => Disjoint (tsupport (F i)) (tsupport (F k))) := by
  have hgood (N : ℕ) : ∀ᶠ i in atTop, ¬loc.terminal (γ i) ∧ N < loc.firstCoordinate (γ i) := by
    have he := (hγ.tendsto_cofinite).eventually ((loc.finite_exceptions j N).eventually_cofinite_notMem)
    rw [Nat.cofinite_eq_atTop] at he
    filter_upwards [he] with i hi
    have hh : ¬(loc.terminal (γ i) ∨ loc.firstCoordinate (γ i) ≤ N) := by
      intro hn
      exact hi ⟨(hj i).le,hn⟩
    simpa only [not_or,not_le] using hh
  obtain ⟨ψ,hψ,hψgood⟩ := choose_mono_sequence hgood
  let f (i : ℕ) (s : C0Ball) := (r (ψ i)).value s*tailProduct (ts (ψ i)) s
  have hf (i : ℕ) : f i ∈ VClass B h :=
    ⟨γ (ψ i),r (ψ i),ts (ψ i),hr _,by rw [hj]; exact hjh,ht _,ha _,rfl⟩
  obtain ⟨H,η,hη,F,hF,hdet,hdis⟩ := tail_separation f (m ∘ ψ) hf hδ
    (half_pos (B.ell_pos j)) (fun i => hd (ψ i)) id tendsto_id (by
      intro i s hs
      have hsu := tsupport_product_subset_left (r (ψ i)).value (tailProduct (ts (ψ i))) hs
      have hh := loc.representation_tail_lower (r (ψ i)) (hψgood i).1 i (hψgood i).2 s hsu
      simpa only [hj,id_eq] using hh)
  exact ⟨H,ψ ∘ η,hψ.comp hη,F,hF,hdet,hdis⟩

end RadiusLocalization
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption OAI.C0Absorption.RadiusLocalization
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.RadiusLocalization.low_bands_disjoint := @_root_.OAI.C0Absorption.RadiusLocalization.low_bands_disjoint
