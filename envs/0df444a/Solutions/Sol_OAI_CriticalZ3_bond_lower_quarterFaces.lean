-- Prove2me | solution 1 for OAI.CriticalZ3.bond_lower_quarterFaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:30:07.242572+00:00
-- url     : https://prove2.me/submissions/04f2cf15-51ac-4911-b5cd-03fb08fbee49

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean:L373-L390
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.bond_lower_quarterFaces. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Theorems.Thm_OAI_CriticalZ3_boundary_eq_union_quarterFace
import Theorems.Thm_OAI_CriticalZ3_exists_lower_forall
import Theorems.Thm_OAI_CriticalZ3_nearestNeighbor_exit_boundary
import Theorems.Thm_OAI_CriticalZ3_quarterFace_preimage
import Theorems.Thm_OAI_CriticalZ3_rtg_first_exit
import Theorems.Thm_OAI_ProductCylinder_continuous_probability
import Theorems.Thm_OAI_ProductCylinder_decreasing_forall

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

theorem bondOpen_neighbor {ω : BondConfig} {x y : Vertex} (h : BondOpen ω x y) :
    NearestNeighbor x y := by
  rcases h with ⟨i,hi,_⟩ | ⟨i,hi,_⟩
  · exact ⟨i,Or.inl hi⟩
  · exact ⟨i,Or.inr hi⟩

/-- An infinite component supplies a finite path to the cube boundary;
this uses no uniqueness or unproved infinite-path theorem. -/
theorem bondSeedInfinite_subset_reachesBoundary (c : Vertex) {m n : ℕ} (hmn : m ≤ n) :
    bondSeedInfinite c m ⊆ bondSeedReaches c m n (cubeBoundary c n) := by
  rintro ω ⟨x,hxm,hx⟩
  have hnot : ¬bondCluster ω x ⊆ cube c n := fun h => hx ((cube_finite c n).subset h)
  obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hnot
  obtain ⟨a,ha,b,hb,hpath,hab⟩ := rtg_first_exit hy (cube_mono c hmn hxm) hyn
  exact ⟨x,hxm,a,nearestNeighbor_exit_boundary ha hb (bondOpen_neighbor hab),hpath⟩

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

theorem bondSeedReaches_determined (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ internalBonds (cube c n) (cube_finite c n), ω' e = ω e) →
      (ω' ∈ bondSeedReaches c m n T ↔ ω ∈ bondSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [bondSeedReaches,Set.mem_ofPred_eq,bondWithin_congr hω]

theorem bondOpen_mono {ω ω' : BondConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : BondOpen ω x y) : BondOpen ω' x y := by
  rcases hxy with ⟨i,hi,hw⟩ | ⟨i,hi,hw⟩
  · exact Or.inl ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (x,i))⟩
  · exact Or.inr ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (y,i))⟩

theorem bondSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ bondSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,y,hy,hp⟩
  refine ⟨x,hx,y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,bondOpen_mono h h'.2.2⟩

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

theorem bondQuarterFace_probability (p : ℝ) (c : Vertex) (m n : ℕ) (f : FaceIndex) :
    bondLaw p (bondSeedReaches c m n (QuarterFace c n f)) =
      bondLaw p (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace)) := by
  let S := faceSymmetry c f
  have hm := ProductCylinder.reindex_probability S.bond (parameter p)
    (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))
    (measurableSet_bondSeedReaches _ _ _ _)
  change bondLaw p _ = bondLaw p _ at hm
  rw [←hm]
  congr 1
  ext ω
  have h := S.bondSeedReaches_map ω 0 m n (QuarterFace c n f)
  simpa only [S,faceSymmetry_zero,quarterFace_preimage,Set.mem_preimage] using h.symm

theorem bondQuarterFace_compl_real (p : ℝ) (c : Vertex) (m n : ℕ) (f : FaceIndex) :
    (bondLaw p).real (bondSeedReaches c m n (QuarterFace c n f))ᶜ =
      (bondLaw p).real (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ := by
  rw [measureReal_compl (measurableSet_bondSeedReaches _ _ _ _),
    measureReal_compl (measurableSet_bondSeedReaches _ _ _ _)]
  simp only [Measure.real_def,bondQuarterFace_probability]

theorem bondBoundary_eq_union_reachesFaces (c : Vertex) (m n : ℕ) :
    bondSeedReaches c m n (cubeBoundary c n) = ⋃ f : FaceIndex, bondSeedReaches c m n (QuarterFace c n f) := by
  ext ω
  simp only [bondSeedReaches,boundary_eq_union_quarterFace,Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x,hx,y,⟨f,hf⟩,hp⟩
    exact ⟨f,x,hx,y,hf,hp⟩
  · rintro ⟨f,x,hx,y,hf,hp⟩
    exact ⟨x,hx,y,⟨f,hf⟩,hp⟩

theorem card_faceIndex : Fintype.card FaceIndex = 24 := by
  norm_num [FaceIndex,Fintype.card_prod,Fintype.card_fun]

theorem bondQuarterFace_Harris (p : ℝ) (m n : ℕ) :
    ((bondLaw p).real (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)^24 ≤
      (bondLaw p).real (bondSeedReaches 0 m n (cubeBoundary 0 n))ᶜ := by
  have h := ProductCylinder.decreasing_forall
    (internalBonds (cube 0 n) (cube_finite 0 n)) (fun _ => parameter p)
    (fun f : FaceIndex => (bondSeedReaches 0 m n (QuarterFace 0 n f))ᶜ)
    (fun f ω ω' hω => not_congr (bondSeedReaches_determined _ _ _ _ ω ω' hω))
    (fun f ω ω' hω h' h => h' (bondSeedReaches_mono _ _ _ _ hω h))
  change (∏ f : FaceIndex, (bondLaw p).real _) ≤ (bondLaw p).real _ at h
  simp_rw [bondQuarterFace_compl_real] at h
  simpa only [Finset.prod_const,Finset.card_univ,card_faceIndex,
    ←Set.compl_iUnion,←bondBoundary_eq_union_reachesFaces] using h

theorem bondQuarterFace_root_bound (p : ℝ) (m n : ℕ) (hmn : m ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    (hseed : (bondLaw p).real (bondSeedInfinite 0 m)ᶜ < ε^24) (c : Vertex) (f : FaceIndex) :
    (bondLaw p).real (bondSeedReaches c m n (QuarterFace c n f))ᶜ < ε := by
  rw [bondQuarterFace_compl_real]
  apply (pow_lt_pow_iff_left₀ (measureReal_nonneg) hε (by norm_num : (24:ℕ) ≠ 0)).mp
  refine (bondQuarterFace_Harris p m n).trans_lt (lt_of_le_of_lt ?_ hseed)
  exact measureReal_mono (Set.compl_subset_compl.mpr (bondSeedInfinite_subset_reachesBoundary 0 hmn))

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

theorem continuous_parameter : Continuous parameter := by
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem continuous_bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Continuous (fun p => (bondLaw p).real (bondSeedReaches c m n T)) :=
  (ProductCylinder.continuous_probability _ _ (bondSeedReaches_determined c m n T)).comp
    (continuous_pi (fun _ => continuous_parameter))

theorem continuous_bondSeedMiss (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Continuous (fun p => (bondLaw p).real (bondSeedReaches c m n T)ᶜ) := by
  simp_rw [measureReal_compl (measurableSet_bondSeedReaches c m n T),probReal_univ]
  exact continuous_const.sub (continuous_bondSeedReaches _ _ _ _)

/-- Quarter-face estimates at any fixed finite family of enclosing radii,
at one parameter below p, uniformly over every center and all 24 faces. -/
theorem bond_lower_quarterFaces {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {m : ℕ} (hseed : (bondLaw p).real (bondSeedInfinite 0 m)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, m ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (bondLaw q).real (bondSeedReaches c m n (QuarterFace c n f)) := by
  obtain ⟨q,hq,hfaces⟩ := exists_lower_forall hp
    (fun n : s => fun t => (bondLaw t).real (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)
    (fun n => continuous_bondSeedMiss _ _ _ _) (fun n =>
      (bondQuarterFace_root_bound p m n (hs n n.property) (by positivity) hseed 0 canonicalFace).trans
        (by linarith : γ/2 < γ))
  refine ⟨q,hq,?_⟩
  intro n hn c f
  have h := hfaces ⟨n,hn⟩
  rw [←bondQuarterFace_compl_real q c m n f,
    measureReal_compl (measurableSet_bondSeedReaches _ _ _ _),probReal_univ] at h
  linarith

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory Classical
open Filter Topology Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.bond_lower_quarterFaces := @_root_.OAI.CriticalZ3.bond_lower_quarterFaces
