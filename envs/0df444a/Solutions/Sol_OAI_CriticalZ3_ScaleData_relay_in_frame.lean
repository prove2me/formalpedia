-- Prove2me | solution 1 for OAI.CriticalZ3.ScaleData.relay_in_frame
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:13:00.895895+00:00
-- url     : https://prove2.me/submissions/a2b9c03c-19b6-40e9-bef4-284be52f38fb

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/RelayProbability.lean:L209-L289
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.ScaleData.relay_in_frame. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_extension_bound
import Theorems.Thm_OAI_CriticalZ3_SignedSymmetry_siteSeedReaches_map
import Theorems.Thm_OAI_LatticeRelay_thirteen_interfaces

-- ---- from OAI.Probability.CriticalZ3.Basic ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uOmega uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory

namespace CriticalZ3

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

open Filter
open scoped Topology

theorem cube_mono (c : Vertex) : Monotone (cube c) := by
  intro m n h x hx
  rw [mem_cube] at hx ⊢
  intro i
  have hn : (m : ℤ) ≤ n := by exact_mod_cast h
  obtain ⟨h₁,h₂⟩ := hx i
  constructor <;> omega

end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

theorem map_restrict (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).map J.restrict = finiteLaw J p := Measure.infinitePi_map_restrict _

theorem cylinder_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (J → Bool)) :
    law p (J.restrict ⁻¹' A) = finiteLaw J p A := by
  rw [←map_restrict,Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite A).measurableSet]

theorem probability_determined (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    law p A = finiteLaw J p {ξ | extend J ξ ∈ A} := by
  rw [←cylinder_probability]
  congr 1
  ext ω
  exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])

theorem measurableSet_determined (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : MeasurableSet A := by
  have he : A = J.restrict ⁻¹' {ξ | extend J ξ ∈ A} := by
    ext ω
    exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

theorem map_reindex (e : E ≃ F) (p : F → Set.Icc (0 : ℝ) 1) :
    (law p).map (fun ω i => ω (e i)) = law (fun i => p (e i)) := by
  have h := Measure.infinitePi_map_piCongrLeft
    (fun i => bernoulliMeasure true false (p (e i))) e.symm
  have he : ((MeasurableEquiv.piCongrLeft (fun _ : E => Bool) e.symm) : (F → Bool) → E → Bool) =
      fun ω i => ω (e i) := by
    funext ω i
    change Equiv.piCongrLeft (fun _ : E => Bool) e.symm ω i = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  simpa only [law,Equiv.apply_symm_apply,he] using h

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI

-- ---- from OAI.Probability.CriticalZ3.Symmetry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

theorem mem_internalBonds {D : Set Vertex} {hD : D.Finite} {e : Bond} :
    e ∈ internalBonds D hD ↔ e.1 ∈ D ∧ step e.1 e.2 ∈ D := by
  simp [internalBonds]

theorem bondWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : BondConfig}
    (hω : ∀ e ∈ internalBonds D hD, ω' e = ω e) :
    Within D (BondOpen ω') = Within D (BondOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,BondOpen]
    apply or_congr
    · apply exists_congr
      intro i
      by_cases he : y = step x i
      · rw [hω (x,i) (mem_internalBonds.mpr ⟨hx,he ▸ hy⟩)]
      · simp [he]
    · apply exists_congr
      intro i
      by_cases he : x = step y i
      · rw [hω (y,i) (mem_internalBonds.mpr ⟨hy,he ▸ hx⟩)]
      · simp [he]
  all_goals simp [Within,hx,hy]

theorem siteWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : SiteConfig}
    (hω : ∀ x ∈ hD.toFinset, ω' x = ω x) :
    Within D (SiteOpen ω') = Within D (SiteOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,SiteOpen,hω x (hD.mem_toFinset.mpr hx),
      hω y (hD.mem_toFinset.mpr hy)]
  all_goals simp [Within,hx,hy]

theorem bondSeedReaches_determined (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ internalBonds (cube c n) (cube_finite c n), ω' e = ω e) →
      (ω' ∈ bondSeedReaches c m n T ↔ ω ∈ bondSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [bondSeedReaches,Set.mem_ofPred_eq,bondWithin_congr hω]

theorem siteSeedReaches_determined (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ (cube_finite c n).toFinset, ω' e = ω e) →
      (ω' ∈ siteSeedReaches c m n T ↔ ω ∈ siteSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [siteSeedReaches,Set.mem_ofPred_eq,siteWithin_congr hω]
  apply exists_congr
  intro x
  by_cases hx : x ∈ cube c m
  · simp only [hx,true_and,hω x ((cube_finite c n).mem_toFinset.mpr (cube_mono c hmn hx))]
  · simp only [hx,false_and]

end CriticalZ3

namespace CriticalZ3
open Classical

namespace SignedSymmetry

theorem bond_apply (S : SignedSymmetry) (e : Bond) :
    S.bond e = (S.vertex e.1+S.edgeShift e.2,S.perm.symm e.2) := rfl

theorem edge_spec (S : SignedSymmetry) (e : Bond) :
    (S.vertex e.1 = (S.bond e).1 ∧ S.vertex (step e.1 e.2) = step (S.bond e).1 (S.bond e).2) ∨
    (S.vertex e.1 = step (S.bond e).1 (S.bond e).2 ∧ S.vertex (step e.1 e.2) = (S.bond e).1) := by
  have hi (i : Fin 3) : (e.2 = S.perm i) ↔ (S.perm.symm e.2 = i) := by
    constructor
    · intro h; rw [h,Equiv.symm_apply_apply]
    · intro h; rw [←h,Equiv.apply_symm_apply]
  by_cases hs : S.signs (S.perm.symm e.2) = true
  · left
    constructor
    · funext i
      simp [bond_apply,edgeShift,hs]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i = true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]
  · right
    constructor
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,he]
      · simp [bond_apply,vertex,edgeShift,step,hs,he]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]

theorem endpoints_map (S : SignedSymmetry) (e : Bond) (x y : Vertex) :
    Endpoints (S.bond e) (S.vertex x) (S.vertex y) ↔ Endpoints e x y := by
  rcases S.edge_spec e with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · unfold Endpoints
    rw [←h₂,←h₁]
    simp only [Equiv.apply_eq_iff_eq]
  · unfold Endpoints
    rw [←h₁,←h₂]
    simp only [Equiv.apply_eq_iff_eq]
    tauto

theorem bondOpen_iff (ω : BondConfig) (x y : Vertex) :
    BondOpen ω x y ↔ ∃ e, ω e = true ∧ Endpoints e x y := by
  constructor
  · rintro (⟨i,h,hω⟩ | ⟨i,h,hω⟩)
    · exact ⟨(x,i),hω,Or.inl ⟨rfl,h⟩⟩
    · exact ⟨(y,i),hω,Or.inr ⟨rfl,h⟩⟩
  · rintro ⟨⟨z,i⟩,hω,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact Or.inl ⟨i,rfl,hω⟩
    · exact Or.inr ⟨i,rfl,hω⟩

theorem bondOpen_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondOpen (fun e => ω (S.bond e)) x y ↔ BondOpen ω (S.vertex x) (S.vertex y) := by
  simp_rw [bondOpen_iff]
  constructor
  · rintro ⟨e,he,hxy⟩
    exact ⟨S.bond e,he,(S.endpoints_map e x y).mpr hxy⟩
  · rintro ⟨e,he,hxy⟩
    refine ⟨S.bond.symm e,by simpa using he,?_⟩
    apply (S.endpoints_map (S.bond.symm e) x y).mp
    simpa using hxy

theorem cube_map (S : SignedSymmetry) (c x : Vertex) (n : ℕ) :
    x ∈ cube c n ↔ S.vertex x ∈ cube (S.vertex c) n := by
  simp only [mem_cube]
  have he (i : Fin 3) :
      (S.vertex c i - (n:ℤ) ≤ S.vertex x i ∧ S.vertex x i ≤ S.vertex c i + (n:ℤ)) ↔
      (c (S.perm i)-(n:ℤ) ≤ x (S.perm i) ∧ x (S.perm i) ≤ c (S.perm i)+(n:ℤ)) := by
    dsimp [vertex]
    cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  simp_rw [he]
  constructor
  · intro h i; exact h _
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)

end SignedSymmetry
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.QuarterFaces ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

universe uE uI uV uW

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

theorem rtg_equiv_iff {V : Type uV} {W : Type uW} (e : V ≃ W) {r : V → V → Prop} {s : W → W → Prop}
    (h : ∀ x y, r x y ↔ s (e x) (e y)) (x y : V) :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · intro hp
    exact Relation.ReflTransGen.lift e (fun a b h' => (h a b).mp h') x y hp
  · intro hp
    have hp' := Relation.ReflTransGen.lift e.symm (fun a b h' =>
      (h (e.symm a) (e.symm b)).mpr (by simpa only [Equiv.apply_symm_apply] using h'))
      (e x) (e y) hp
    simpa only [Function.onFun,Equiv.symm_apply_apply] using hp'

namespace SignedSymmetry

theorem bondWithin_map (S : SignedSymmetry) (ω : BondConfig) (c : Vertex) (n : ℕ) (x y : Vertex) :
    Within (cube c n) (BondOpen (fun e => ω (S.bond e))) x y ↔
      Within (cube (S.vertex c) n) (BondOpen ω) (S.vertex x) (S.vertex y) := by
  simp only [Within,S.cube_map c x n,S.cube_map c y n,S.bondOpen_map]

theorem bondSeedReaches_map (S : SignedSymmetry) (ω : BondConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.bond e)) ∈ bondSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ bondSeedReaches (S.vertex c) m n T := by
  change (∃ x ∈ cube c m, ∃ y, S.vertex y ∈ T ∧ _) ↔ _
  simp_rw [rtg_equiv_iff S.vertex (S.bondWithin_map ω c n)]
  constructor
  · rintro ⟨x,hx,y,hy,hp⟩
    exact ⟨S.vertex x,(S.cube_map c x m).mp hx,S.vertex y,hy,hp⟩
  · rintro ⟨x,hx,y,hy,hp⟩
    refine ⟨S.vertex.symm x,?_,S.vertex.symm y,?_,?_⟩
    · exact (S.cube_map c _ m).mpr (by simpa only [Equiv.apply_symm_apply] using hx)
    · simpa only [Equiv.apply_symm_apply] using hy
    · simpa only [Equiv.apply_symm_apply] using hp

end SignedSymmetry

end CriticalZ3

namespace ProductCylinder

theorem reindex_probability {E : Type uE} (e : E ≃ E) (p : Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    law (fun _ => p) ((fun ω i => ω (e i)) ⁻¹' A) = law (fun _ => p) A := by
  rw [←Measure.map_apply (Measurable.of_eval (fun i => measurable_pi_apply (e i))) hA,
    map_reindex]

end ProductCylinder

namespace CriticalZ3
open Classical

theorem measurableSet_bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    MeasurableSet (bondSeedReaches c m n T) :=
  ProductCylinder.measurableSet_determined _ _ (bondSeedReaches_determined c m n T)

theorem measurableSet_siteSeedReaches (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    MeasurableSet (siteSeedReaches c m n T) :=
  ProductCylinder.measurableSet_determined _ _ (siteSeedReaches_determined c m n hmn T)

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ShellProbability ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

end FiniteAssociation

namespace ProductCylinder
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem probability_congr_parameters (J : Finset E)
    (p q : E → Set.Icc (0 : ℝ) 1) (hpq : ∀ e ∈ J, p e = q e)
    (A : Set (E → Bool)) (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    (law p).real A = (law q).real A := by
  simp only [Measure.real_def,probability_determined J _ A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))]
  congr 2
  unfold finiteLaw
  congr 1
  funext e
  rw [hpq e e.2]

end ProductCylinder

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

end OAI

-- ---- from OAI.Probability.CriticalZ3.SeedQuality ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

end Model

namespace Box

theorem contains_cube_iff {c x : Vertex} {n : ℕ} : (cube c n).Contains x ↔ x ∈ CriticalZ3.cube c n :=
  mem_cube.symm

theorem cube_bonds_eq (c : Vertex) (r : ℕ) :
    (cube c r).bonds = internalBonds (CriticalZ3.cube c r) (cube_finite c r) := by
  ext e
  simp only [mem_bonds,mem_internalBonds,contains_cube_iff]

theorem cube_sites_eq (c : Vertex) (r : ℕ) :
    (cube c r).vertices = (cube_finite c r).toFinset := by
  ext e
  simp only [mem_vertices,Set.Finite.mem_toFinset,contains_cube_iff]
end Box

namespace Model

theorem seedReaches_determined (m : Model) (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) ((Box.cube c b).bits m)
      (fun ω => ω ∈ m.SeedReaches c a b T) := by
  intro ω ω' h
  apply propext
  cases m
  · rw [seedReaches_bond]
    apply bondSeedReaches_determined c a b T ω ω'
    simpa only [Box.bits,Box.cube_bonds_eq] using h
  · apply siteSeedReaches_determined c a b hab T ω ω'
    simpa only [Box.bits,Box.cube_sites_eq] using h
end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Scales ----
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

end CriticalScales

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Model
end Model

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem q_pos : 0 < (s.q:ℝ) := (half_pos s.p_pos).trans s.q_half

theorem successCard_le : Box.successCard model s.seed ≤ Box.seedCard model s.seed+1 := by
  cases model <;> simp [Box.successCard]

theorem success_bound : (s.p/2)^(Box.seedCard model s.seed+1) ≤
    (s.q:ℝ)^Box.successCard model s.seed := by
  exact (pow_le_pow_left₀ (by linarith [s.p_pos]) s.q_half.le _).trans
    (pow_le_pow_of_le_one s.q.property.1 s.q.property.2 s.successCard_le)

theorem extension_budget :
    1/((1-s.p)^(s.K*(8*s.seed+5)^3)*(s.R-s.seed:ℕ)) +
      4/((s.K:ℝ)*(s.q:ℝ)^Box.successCard model s.seed)+2*s.γ/s.τ+s.τ < s.η := by
  have hh : 4/((s.K:ℝ)*(s.q:ℝ)^Box.successCard model s.seed) ≤
      4/((s.K:ℝ)*(s.p/2)^(Box.seedCard model s.seed+1)) := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (by exact_mod_cast s.K_pos) (pow_pos (half_pos s.p_pos) _))
    exact mul_le_mul_of_nonneg_left s.success_bound (Nat.cast_nonneg _)
  linarith [s.R_budget,s.K_budget,s.trial_budget,s.relay_budget]
end ScaleData
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Relay ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace LatticeRelay
open Set
theorem P_thirteen_subset {r R : ℤ} (_hR : 0 < R) (hr : 100*(R+1) < r) :
    P r R 13 ⊆ Cube (axisCenter (20*r+1)) (4*r) := by
  intro x hx i
  have h := hx i
  simp only [routeCenter,routeWidths,show ¬13 ≤ 3 by omega,ite_false,
    show ¬13 ≤ 12 by omega] at h
  change |x i-axisCenter (20*r+1) i| ≤ 4*r
  dsimp at h
  omega

theorem expanded_route_subset_prism {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {i : ℕ} (hi : i < 13) :
    Expand (routeCenter r i) (routeWidths r R i) R ⊆ Prism r := by
  intro u hu
  obtain ⟨s,hs,hsub,_⟩ := thirteen_interfaces hR hr hi u hu
  apply hsub
  intro j
  change |u j-u j| ≤ s
  simp only [sub_self,abs_zero]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hs
  rcases hs with rfl|rfl|rfl <;> omega

end LatticeRelay

end OAI

-- ---- from OAI.Probability.CriticalZ3.RelayProbability ----
namespace OAI

universe uOmega

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Model

theorem box_internal (m : Model) (B : Box) (e : m.Bit) :
    e ∈ B.bits m ↔ m.Internal {x | B.Contains x} e := by
  cases m <;> simp [Box.bits,Internal]

theorem internal_mono (m : Model) {D T : Set Vertex} (h : D ⊆ T) {e : m.Bit}
    (he : m.Internal D e) : m.Internal T e := by
  cases m
  · exact ⟨h he.1,h he.2⟩
  · exact h he

theorem UniformOn.box (m : Model) {p : m.Bit → Set.Icc (0:ℝ) 1} {q : Set.Icc (0:ℝ) 1}
    {D : Set Vertex} (h : m.UniformOn p q D) (B : Box) (hB : ∀ x, B.Contains x → x ∈ D) :
    ∀ e ∈ B.bits m, p e = q := fun e he => h e (m.internal_mono hB ((m.box_internal B e).mp he))

theorem seedReaches_target_mono (m : Model) (c : Vertex) (a b : ℕ) {T U : Set Vertex} (h : T ⊆ U) :
    m.SeedReaches c a b T ⊆ m.SeedReaches c a b U := by
  rintro ω ⟨x,hx,ho,y,hy,hp⟩
  exact ⟨x,hx,ho,y,h hy,hp⟩

theorem seedReaches_image_probability (m : Model) (S : SignedSymmetry) (q : Set.Icc (0:ℝ) 1)
    (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    (ProductCylinder.law (fun _ : m.Bit => q)).real
      (m.SeedReaches (S.vertex c) a b (S.vertex '' T)) =
    (ProductCylinder.law (fun _ : m.Bit => q)).real (m.SeedReaches c a b T) := by
  have he : S.vertex ⁻¹' (S.vertex '' T) = T := Set.preimage_image_eq T S.vertex.injective
  cases m
  · simp only [seedReaches_bond,Measure.real_def]
    have hh := ProductCylinder.reindex_probability S.bond q (bondSeedReaches c a b T)
      (measurableSet_bondSeedReaches _ _ _ _)
    rw [←hh]
    congr 2
    ext ω
    simpa only [Set.mem_preimage,he] using (S.bondSeedReaches_map ω c a b (S.vertex '' T)).symm
  · simp only [seedReaches_site,Measure.real_def]
    have hh := ProductCylinder.reindex_probability S.vertex q (siteSeedReaches c a b T)
      (measurableSet_siteSeedReaches _ _ _ hab _)
    rw [←hh]
    congr 2
    ext ω
    simpa only [Set.mem_preimage,he] using (S.siteSeedReaches_map ω c a b (S.vertex '' T)).symm
end Model

namespace LatticeGraph
variable (G : LatticeGraph)
theorem ContainsSet.box {D : Set Vertex} (h : G.ContainsSet D) (B : Box)
    (hB : ∀ x, B.Contains x → x ∈ D) : G.ContainsBox B := by
  constructor
  · intro x hx; exact h.1 x (hB x (Box.mem_vertices B x |>.mp hx))
  · intro e he
    have hh := (Box.mem_bonds B e).mp he
    exact h.2 e (hB _ hh.1) (hB _ hh.2)
end LatticeGraph

namespace Box

theorem contains_rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (rect c w hw).Contains x ↔ x ∈ LatticeRelay.Rect c w := by
  constructor <;> intro h i
  · have hh := h i
    change |x i-c i| ≤ w i
    rw [abs_le]
    dsimp [rect] at hh
    omega
  · have hh := h i
    change |x i-c i| ≤ w i at hh
    rw [abs_le] at hh
    change c i-w i ≤ x i ∧ x i ≤ c i+w i
    omega

theorem abs_vertex_sub (S : SignedSymmetry) (x c : Vertex) (i : Fin 3) :
    |S.vertex x i-S.vertex c i| = |x (S.perm i)-c (S.perm i)| := by
  dsimp [SignedSymmetry.vertex]
  cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · have he : S.shift i+-x (S.perm i)-(S.shift i+-c (S.perm i)) =
        -(x (S.perm i)-c (S.perm i)) := by ring
    rw [he,abs_neg]
  · congr 1; ring

theorem framedRect_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (framedRect S c w hw).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Rect c w := by
  rw [framedRect,contains_rect]
  change (∀ i, |S.vertex x i-S.vertex c i| ≤ w (S.perm i)) ↔ _
  simp_rw [abs_vertex_sub]
  constructor
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)
  · intro h i; exact h _

theorem framedRect_expand_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i)
    (R : ℕ) (x : Vertex) :
    ((framedRect S c w hw).expand R).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Expand c w R := by
  have he : (framedRect S c w hw).expand R =
      framedRect S c (fun i => w i+R) (fun i => by have := hw i; positivity) := by
    apply Box.ext <;> funext i <;> dsimp [expand,framedRect,rect] <;> ring
  rw [he,framedRect_map]
  rfl
end Box

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem radius_seed {n : ℕ} (hn : n ∈ ({2*s.r,2*s.r+1,10*s.r} : Finset ℕ)) : s.seed ≤ n := by
  have := s.seed_R
  have := s.large_r
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

theorem extension_interface (G : LatticeGraph) (p : model.Bit → Set.Icc (0:ℝ) 1)
    (D : Set Vertex) (hG : G.ContainsSet D) (hp : model.UniformOn p s.q D)
    (o : G.Node) (ho : o.1 ∉ D) (B : Box) (T : Set Vertex)
    (hB : ∀ x, (B.expand s.R).Contains x → x ∈ D)
    (hI : ∀ u, (B.expand s.R).Contains u → ∃ n ∈ ({2*s.r,2*s.r+1,10*s.r}:Finset ℕ),
      ∃ S : SignedSymmetry, ∃ c : Vertex, ∃ f : FaceIndex, S.vertex c = u ∧
      (∀ x ∈ cube u n, x ∈ D) ∧ S.vertex '' QuarterFace c n f ⊆ T) :
    (ProductCylinder.law p).real {ω | G.Meets model ω o {x | B.Contains x} ∧
      ¬G.Meets model ω o T} < s.η := by
  refine (G.extension_bound model p s.q s.q_pos s.q_lt.le s.p_lt_one B s.seed s.K s.R
    s.K_pos s.seed_R (hG.box G _ hB) o T (fun h => ho (hB _ h))
    (hp.box model _ hB) s.γ_range.1.le s.τ_range.1 ?_).trans_lt s.extension_budget
  intro u hu
  obtain ⟨n,hn,S,c,f,hc,hcube,hface⟩ := hI u hu
  have hr := s.radius_seed hn
  refine ⟨n,hr,hG.box G _ (fun x hx => hcube x (Box.contains_cube_iff.mp hx)),?_⟩
  have he := ProductCylinder.probability_congr_parameters ((Box.cube u n).bits model)
    p (fun _ => s.q) (hp.box model _ (fun x hx => hcube x (Box.contains_cube_iff.mp hx)))
    (model.SeedReaches u s.seed n T) (model.seedReaches_determined _ _ _ hr _)
  rw [he]
  have hh := s.faces n hn c f
  rw [←model.seedReaches_image_probability S s.q c s.seed n hr (QuarterFace c n f),hc] at hh
  exact hh.le.trans (measureReal_mono (model.seedReaches_target_mono _ _ _ hface))
end ScaleData
end CriticalZ3

namespace MeasureTheory
open scoped _root_.MeasureTheory
open Classical
variable {Ω : Type uOmega} [MeasurableSpace Ω]
theorem finite_relay_bound (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsProbabilityMeasure μ] (A : ℕ → Set Ω)
    (η : ℝ) (n : ℕ) (h : ∀ i < n, μ.real (A i \ A (i+1)) ≤ η) :
    μ.real (A 0 \ A n) ≤ n*η := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul,Set.sdiff_self,_root_.MeasureTheory.measureReal_empty,le_refl]
  | succ n ih =>
    have hs : A 0 \ A (n+1) ⊆ (A 0 \ A n) ∪ (A n \ A (n+1)) := by
      intro ω hω
      by_cases hn : ω ∈ A n
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    have hh := (_root_.MeasureTheory.measureReal_mono (μ := μ) hs).trans (_root_.MeasureTheory.measureReal_union_le _ _)
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    rw [Nat.cast_add,Nat.cast_one]
    nlinarith
end MeasureTheory

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem R_pos : 0 < s.R := s.seed_pos.trans s.seed_R

theorem routeBox_contains (S : SignedSymmetry) (i : ℕ) (x : Vertex) :
    (s.routeBox S i).Contains x ↔ x ∈ S.vertex '' LatticeRelay.P s.r s.R i := by
  rw [←S.vertex.apply_symm_apply x,routeBox,Box.framedRect_map]
  simp only [Set.mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]
  rfl

theorem relay_in_frame (G : LatticeGraph) (p : model.Bit → Set.Icc (0:ℝ) 1)
    (S : SignedSymmetry) (hG : G.ContainsSet (S.vertex '' LatticeRelay.Prism s.r))
    (hp : model.UniformOn p s.q (S.vertex '' LatticeRelay.Prism s.r))
    (o : G.Node) (ho : o.1 ∉ S.vertex '' LatticeRelay.Prism s.r) :
    (ProductCylinder.law p).real
      {ω | G.Meets model ω o (cube (S.vertex 0) (4*s.r)) ∧
        ¬G.Meets model ω o (cube (S.vertex (LatticeRelay.axisCenter (20*s.r+1))) (4*s.r))}
      ≤ 13*s.η := by
  have hR : (0:ℤ) < s.R := by exact_mod_cast s.R_pos
  have hr : (100:ℤ)*(s.R+1) < s.r := by exact_mod_cast s.large_r
  have hcube (c : Vertex) (n : ℕ) : S.vertex '' LatticeRelay.Cube c n = cube (S.vertex c) n := by
    ext x
    rw [←S.vertex.apply_symm_apply x]
    simp only [Set.mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]
    rw [←S.cube_map]
    rw [mem_cube]
    constructor <;> intro h i
    · have hh := h i
      change |S.vertex.symm x i-c i| ≤ (n:ℤ) at hh
      rw [abs_le] at hh
      change c i-n ≤ S.vertex.symm x i ∧ S.vertex.symm x i ≤ c i+n
      omega
    · have hh := h i
      change c i-n ≤ S.vertex.symm x i ∧ S.vertex.symm x i ≤ c i+n at hh
      change |S.vertex.symm x i-c i| ≤ (n:ℤ)
      rw [abs_le]
      omega
  let A (i : ℕ) : Set model.Config := {ω | G.Meets model ω o {x | (s.routeBox S i).Contains x}}
  have hi (i : ℕ) (hi : i < 13) : (ProductCylinder.law p).real (A i \ A (i+1)) ≤ s.η := by
    apply le_of_lt
    apply s.extension_interface G p (S.vertex '' LatticeRelay.Prism s.r) hG hp o ho
      (s.routeBox S i) {x | (s.routeBox S (i+1)).Contains x}
    · intro x hx
      refine ⟨S.vertex.symm x,?_,S.vertex.apply_symm_apply x⟩
      apply LatticeRelay.expanded_route_subset_prism hR hr hi
      apply (Box.framedRect_expand_map S _ _ (s.route_width_nonneg i) s.R (S.vertex.symm x)).mp
      simpa only [routeBox,Equiv.apply_symm_apply] using hx
    · intro u hu
      have huu : S.vertex.symm u ∈ LatticeRelay.Expand
          (LatticeRelay.routeCenter s.r i) (LatticeRelay.routeWidths s.r s.R i) s.R := by
        apply (Box.framedRect_expand_map S _ _ (s.route_width_nonneg i) s.R (S.vertex.symm u)).mp
        simpa only [routeBox,Equiv.apply_symm_apply] using hu
      obtain ⟨n,hn,hsub,j,signs,hface⟩ := LatticeRelay.thirteen_interfaces hR hr hi _ huu
      have hn' : ∃ l ∈ ({2*s.r,2*s.r+1,10*s.r}:Finset ℕ), (l:ℤ) = n := by
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hn
        rcases hn with rfl|rfl|rfl
        · exact ⟨2*s.r,by simp,by push_cast; rfl⟩
        · exact ⟨2*s.r+1,by simp,by push_cast; rfl⟩
        · exact ⟨10*s.r,by simp,by push_cast; rfl⟩
      obtain ⟨l,hl,rfl⟩ := hn'
      refine ⟨l,hl,S,S.vertex.symm u,(j,signs),S.vertex.apply_symm_apply u,?_,?_⟩
      · intro x hx
        have hx' : x ∈ S.vertex '' LatticeRelay.Cube (S.vertex.symm u) l := by
          rw [hcube,S.vertex.apply_symm_apply]
          exact hx
        obtain ⟨y,hy,rfl⟩ := hx'
        exact ⟨y,hsub hy,rfl⟩
      · rintro x ⟨y,hy,rfl⟩
        apply (s.routeBox_contains S (i+1) _).mpr
        exact ⟨y,hface hy,rfl⟩
  have h := finite_relay_bound (ProductCylinder.law p) A s.η 13 hi
  norm_num only [Nat.cast_ofNat] at h
  apply le_trans (measureReal_mono (μ := ProductCylinder.law p) ?_) h
  intro ω hω
  constructor
  · obtain ⟨y,hy,hconn⟩ := hω.1
    refine ⟨y,?_,hconn⟩
    apply (s.routeBox_contains S 0 _).mpr
    rw [LatticeRelay.P_zero,show (4:ℤ)*s.r = (4*s.r:ℕ) by push_cast; rfl,hcube]
    exact hy
  · intro hh
    apply hω.2
    obtain ⟨y,hy,hconn⟩ := hh
    refine ⟨y,?_,hconn⟩
    have hy' := (s.routeBox_contains S 13 _).mp hy
    obtain ⟨z,hz,hzy⟩ := hy'
    rw [←hzy]
    have hz' := LatticeRelay.P_thirteen_subset hR hr hz
    have hm : S.vertex z ∈ S.vertex '' LatticeRelay.Cube (LatticeRelay.axisCenter (20*s.r+1)) (4*s.r:ℕ) :=
      ⟨z,by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz',rfl⟩
    rwa [hcube] at hm
end ScaleData
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.ScaleData
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.ScaleData.relay_in_frame := @_root_.OAI.CriticalZ3.ScaleData.relay_in_frame
