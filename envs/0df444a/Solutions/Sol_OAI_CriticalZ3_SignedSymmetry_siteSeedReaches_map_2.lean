-- Prove2me | solution 2 for OAI.CriticalZ3.SignedSymmetry.siteSeedReaches_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:25:07.62145+00:00
-- url     : https://prove2.me/submissions/d87c4667-b314-4cb1-930a-ca8baab3b1fb

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean:L105-L119
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.SignedSymmetry.siteSeedReaches_map. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

-- ---- from OAI.Probability.CriticalZ3.Symmetry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

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

theorem neighbor_map (S : SignedSymmetry) (x y : Vertex) :
    NearestNeighbor x y ↔ NearestNeighbor (S.vertex x) (S.vertex y) := by
  have he (x y : Vertex) : NearestNeighbor x y ↔ BondOpen (fun _ => true) x y := by
    simp only [NearestNeighbor,BondOpen,and_true]
    rw [exists_or]
  simpa only [he] using S.bondOpen_map (fun _ => true) x y

theorem siteOpen_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteOpen (fun e => ω (S.vertex e)) x y ↔ SiteOpen ω (S.vertex x) (S.vertex y) := by
  simp only [SiteOpen,←S.neighbor_map]

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

theorem siteWithin_map (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (n : ℕ) (x y : Vertex) :
    Within (cube c n) (SiteOpen (fun e => ω (S.vertex e))) x y ↔
      Within (cube (S.vertex c) n) (SiteOpen ω) (S.vertex x) (S.vertex y) := by
  simp only [Within,S.cube_map c x n,S.cube_map c y n,S.siteOpen_map]

theorem siteSeedReaches_map (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ siteSeedReaches (S.vertex c) m n T := by
  change (∃ x ∈ cube c m, ω (S.vertex x) = true ∧ ∃ y, S.vertex y ∈ T ∧ _) ↔ _
  simp_rw [rtg_equiv_iff S.vertex (S.siteWithin_map ω c n)]
  constructor
  · rintro ⟨x,hx,hw,y,hy,hp⟩
    exact ⟨S.vertex x,(S.cube_map c x m).mp hx,hw,S.vertex y,hy,hp⟩
  · rintro ⟨x,hx,hw,y,hy,hp⟩
    refine ⟨S.vertex.symm x,?_,?_,S.vertex.symm y,?_,?_⟩
    · exact (S.cube_map c _ m).mpr (by simpa only [Equiv.apply_symm_apply] using hx)
    · simpa only [Equiv.apply_symm_apply] using hw
    · simpa only [Equiv.apply_symm_apply] using hy
    · simpa only [Equiv.apply_symm_apply] using hp

end SignedSymmetry

end CriticalZ3

namespace ProductCylinder

end ProductCylinder

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.SignedSymmetry
open MeasureTheory ProbabilityTheory Classical
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.SignedSymmetry.siteSeedReaches_map := @_root_.OAI.CriticalZ3.SignedSymmetry.siteSeedReaches_map
