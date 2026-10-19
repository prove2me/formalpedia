-- Prove2me | solution 1 for OAI.C0Absorption.tail_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:20:03.74747+00:00
-- url     : https://prove2.me/submissions/180c5fe3-8650-46a2-8fa9-43d90f356032

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Supports.lean:L33-L89
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.tail_separation. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_VClass_lipschitz
import Theorems.Thm_OAI_C0Absorption_completedPairing_tendsto

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

theorem tau_antitone (s : C0) : Antitone (fun N => tau N s) := by
  intro M N hMN
  apply c0_norm_le _ (tau_nonneg M s)
  intro i
  rw [coordinateTail_apply]
  split_ifs with hi
  · have hh := c0_norm_apply_le (coordinateTail M s) i
    simpa [tau, coordinateTail_apply, lt_of_le_of_lt hMN hi] using hh
  · simpa using tau_nonneg M s

theorem tailFactor_eq_one {c : ℝ} (hc : 0 < c) (N : ℕ) (s : C0) (hs : tau N s ≤ c) :
    tailFactor c N s = 1 := by
  apply min_eq_left
  apply (le_max_left _ _).trans'
  have hdiv := (div_le_one hc).mpr hs
  linarith

theorem tailFactor_eq_zero {c : ℝ} (hc : 0 < c) (N : ℕ) (s : C0) (hs : 2*c ≤ tau N s) :
    tailFactor c N s = 0 := by
  have hdiv : 2 ≤ tau N s/c := (le_div_iff₀ hc).mpr hs
  simp [tailFactor, max_eq_right (show 2-tau N s/c ≤ 0 by linarith)]

theorem tailFactor_tendsto_one {c : ℝ} (hc : 0 < c) (s : C0) :
    Tendsto (fun N => tailFactor c N s) atTop (nhds 1) := by
  have hh : ∀ᶠ N in atTop, tau N s ≤ c :=
    (tau_tendsto_zero s).eventually (eventually_le_nhds hc)
  apply tendsto_const_nhds.congr'
  filter_upwards [hh] with N hN
  exact (tailFactor_eq_one hc N s hN).symm

theorem tailFactor_support {c : ℝ} (hc : 0 < c) (N : ℕ) :
    tsupport (tailFactor c N) ⊆ {s | tau N s ≤ 2*c} := by
  apply closure_minimal
  · intro s hs
    by_contra hh
    exact hs (tailFactor_eq_zero hc N s (le_of_not_ge hh))
  · exact isClosed_le (tau_lipschitz N).continuous continuous_const

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

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

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

theorem thin_sequence {r : ℕ → ℕ → Prop} (hr : ∀ i, ∀ᶠ j in atTop, r i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j, i < j → r (φ i) (φ j) := by
  have he (t : Set ℕ) (ht : t.Finite) : ∀ᶠ j in atTop, ∀ i ∈ t, i<j ∧ r i j :=
    (eventually_all_finite ht).mpr (fun i _ => (eventually_gt_atTop i).and (hr i))
  obtain ⟨φ,hφ⟩ := seq_of_forall_finite_exists (fun t ht => (he t ht).exists)
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_comm.mp hφ.1, forall_comm.mp hφ.2⟩

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

theorem tsupport_product_subset_right {X : Type*} [TopologicalSpace X] (f g : X → ℝ) :
    tsupport (fun x => f x*g x) ⊆ tsupport g := by
  simpa only [mul_comm] using tsupport_product_subset_left g f

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_mul_tail {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ VClass B h) (a N : ℕ) :
    (fun s => f s*tailFactor (dyadic a) (N+1) s.val) ∈ VClass B (h+a+1) := by
  obtain ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩ := hf
  let t : TailOperation := ⟨a,N,true⟩
  refine ⟨γ,r,t::ts,by omega,by omega,by simpa using (show ts.length+1 ≤ h+a+1 by omega),?_,?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · change a ≤ h+a+1; omega
    · have hh := hs q hq; omega
  · funext s
    simp only [tailProduct_cons, t, TailOperation.factor, ↓reduceIte]
    ring

theorem tail_separation {h : ℕ} (F : ℕ → C0Ball → ℝ) (m : ℕ → SourceSpace B)
    (hF : ∀ i, F i ∈ VClass B h) {δ cstar : ℝ} (hδ : 0 < δ) (hcstar : 0 < cstar)
    (hdetect : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hsupport : ∀ i s, s ∈ tsupport (F i) → cstar ≤ tau (M i) s.val) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℕ → C0Ball → ℝ,
      (∀ i, G i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (G i) (m (φ i))|) ∧
      Pairwise (fun i j => Disjoint (tsupport (G i)) (tsupport (G j))) := by
  have he : ∀ᶠ a in atTop, dyadic a < cstar/2 :=
    dyadic_tendsto.eventually (eventually_lt_nhds (half_pos hcstar))
  obtain ⟨a,ha⟩ := he.exists
  let H := h+a+1
  let f (i N : ℕ) (s : C0Ball) := F i s*tailFactor (dyadic a) (N+1) s.val
  have hf (i N : ℕ) : f i N ∈ VClass B H := VClass_mul_tail (hF i) a N
  obtain ⟨A,hA⟩ := VClass_pairing_bound B H
  have hconv (i : ℕ) : Tendsto
      (fun N => completedPairing (sourceClasses B) c0Origin (f i N) (m i)) atTop
      (nhds (completedPairing (sourceClasses B) c0Origin (F i) (m i))) := by
    apply (completedPairing_tendsto (sourceClasses B) c0Origin (f i) (F i) A
      (fun N => hA (f i N) (hf i N)) ?_).2
    intro s
    have hh := (tailFactor_tendsto_one (dyadic_pos a) s.val).comp
      (tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id)
    simpa only [f,mul_one,Function.comp_def,Nat.succ_eq_add_one] using hh.const_mul (F i s)
  have hchoose (i : ℕ) : ∃ N, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (f i N) (m i)| := by
    have hev := (Metric.tendsto_nhds.mp (hconv i)) (δ/2) (half_pos hδ)
    obtain ⟨N,hN⟩ := hev.exists
    refine ⟨N,?_⟩
    rw [Real.dist_eq] at hN
    have hab := abs_sub_abs_le_abs_sub
      (completedPairing (sourceClasses B) c0Origin (F i) (m i))
      (completedPairing (sourceClasses B) c0Origin (f i N) (m i))
    rw [abs_sub_comm] at hab
    linarith [hdetect i]
  choose N hN using hchoose
  obtain ⟨φ,hφ,hrel⟩ := thin_sequence (r := fun i j => N i+1 ≤ M j) (fun i =>
    hM.eventually (eventually_ge_atTop (N i+1)))
  refine ⟨H,φ,hφ,fun i => f (φ i) (N (φ i)),fun i => hf _ _,fun i => hN _,?_⟩
  have hdis (i j : ℕ) (hij : i<j) : Disjoint
      (tsupport (f (φ i) (N (φ i)))) (tsupport (f (φ j) (N (φ j)))) := by
    apply Set.disjoint_left.mpr
    intro s hi hj
    have hi' := tsupport_product_subset_right (F (φ i))
      (fun s : C0Ball => tailFactor (dyadic a) (N (φ i)+1) s.val) hi
    have hi'' := tsupport_comp_subset (tailFactor (dyadic a) (N (φ i)+1)) continuous_subtype_val hi'
    have hupper := tailFactor_support (dyadic_pos a) (N (φ i)+1) hi''
    have hj' := tsupport_product_subset_left (F (φ j))
      (fun s : C0Ball => tailFactor (dyadic a) (N (φ j)+1) s.val) hj
    have hlower := hsupport (φ j) s hj'
    have hord := tau_antitone s.val (hrel i j hij)
    change tau (N (φ i)+1) s.val ≤ 2*dyadic a at hupper
    linarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hdis i j hlt
  · exact (hdis j i hgt).symm

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


theorem solution : type_of% @_root_.OAI.C0Absorption.tail_separation := @_root_.OAI.C0Absorption.tail_separation
