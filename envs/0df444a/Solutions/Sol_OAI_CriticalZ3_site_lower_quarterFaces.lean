-- Prove2me | solution 1 for OAI.CriticalZ3.site_lower_quarterFaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:32:08.545341+00:00
-- url     : https://prove2.me/submissions/e66ccd16-4900-44e4-9c66-f790e731878f

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean:L392-L407
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.site_lower_quarterFaces. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Theorems.Thm_OAI_CriticalZ3_SignedSymmetry_siteSeedReaches_map
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

theorem siteSeedInfinite_subset_reachesBoundary (c : Vertex) {m n : ℕ} (hmn : m ≤ n) :
    siteSeedInfinite c m ⊆ siteSeedReaches c m n (cubeBoundary c n) := by
  rintro ω ⟨x,hxm,hx⟩
  have hnot : ¬siteCluster ω x ⊆ cube c n := fun h => hx ((cube_finite c n).subset h)
  obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hnot
  obtain ⟨a,ha,b,hb,hpath,hab⟩ := rtg_first_exit hy.2 (cube_mono c hmn hxm) hyn
  exact ⟨x,hxm,hy.1,a,nearestNeighbor_exit_boundary ha hb hab.1,hpath⟩

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

theorem siteWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : SiteConfig}
    (hω : ∀ x ∈ hD.toFinset, ω' x = ω x) :
    Within D (SiteOpen ω') = Within D (SiteOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,SiteOpen,hω x (hD.mem_toFinset.mpr hx),
      hω y (hD.mem_toFinset.mpr hy)]
  all_goals simp [Within,hx,hy]

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

theorem siteOpen_mono {ω ω' : SiteConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : SiteOpen ω x y) : SiteOpen ω' x y :=
  ⟨hxy.1,Bool.eq_true_of_true_le (hxy.2.1 ▸ h x),Bool.eq_true_of_true_le (hxy.2.2 ▸ h y)⟩

theorem siteSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ siteSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,hω,y,hy,hp⟩
  refine ⟨x,hx,Bool.eq_true_of_true_le (hω ▸ h x),y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,siteOpen_mono h h'.2.2⟩

end CriticalZ3

namespace CriticalZ3
open Classical

namespace SignedSymmetry

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

namespace SignedSymmetry

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

theorem measurableSet_siteSeedReaches (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    MeasurableSet (siteSeedReaches c m n T) :=
  ProductCylinder.measurableSet_determined _ _ (siteSeedReaches_determined c m n hmn T)

theorem siteQuarterFace_probability (p : ℝ) (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (f : FaceIndex) :
    siteLaw p (siteSeedReaches c m n (QuarterFace c n f)) =
      siteLaw p (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace)) := by
  let S := faceSymmetry c f
  have hm := ProductCylinder.reindex_probability S.vertex (parameter p)
    (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))
    (measurableSet_siteSeedReaches _ _ _ hmn _)
  change siteLaw p _ = siteLaw p _ at hm
  rw [←hm]
  congr 1
  ext ω
  have h := S.siteSeedReaches_map ω 0 m n (QuarterFace c n f)
  simpa only [S,faceSymmetry_zero,quarterFace_preimage,Set.mem_preimage] using h.symm

theorem siteQuarterFace_compl_real (p : ℝ) (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (f : FaceIndex) :
    (siteLaw p).real (siteSeedReaches c m n (QuarterFace c n f))ᶜ =
      (siteLaw p).real (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ := by
  rw [measureReal_compl (measurableSet_siteSeedReaches _ _ _ hmn _),
    measureReal_compl (measurableSet_siteSeedReaches _ _ _ hmn _)]
  simp only [Measure.real_def,siteQuarterFace_probability p c m n hmn]

theorem siteBoundary_eq_union_reachesFaces (c : Vertex) (m n : ℕ) :
    siteSeedReaches c m n (cubeBoundary c n) = ⋃ f : FaceIndex, siteSeedReaches c m n (QuarterFace c n f) := by
  ext ω
  simp only [siteSeedReaches,boundary_eq_union_quarterFace,Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x,hx,hw,y,⟨f,hf⟩,hp⟩
    exact ⟨f,x,hx,hw,y,hf,hp⟩
  · rintro ⟨f,x,hx,hw,y,hf,hp⟩
    exact ⟨x,hx,hw,y,⟨f,hf⟩,hp⟩

theorem card_faceIndex : Fintype.card FaceIndex = 24 := by
  norm_num [FaceIndex,Fintype.card_prod,Fintype.card_fun]

theorem siteQuarterFace_Harris (p : ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ((siteLaw p).real (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)^24 ≤
      (siteLaw p).real (siteSeedReaches 0 m n (cubeBoundary 0 n))ᶜ := by
  have h := ProductCylinder.decreasing_forall
    (cube_finite 0 n).toFinset (fun _ => parameter p)
    (fun f : FaceIndex => (siteSeedReaches 0 m n (QuarterFace 0 n f))ᶜ)
    (fun f ω ω' hω => not_congr (siteSeedReaches_determined _ _ _ hmn _ ω ω' hω))
    (fun f ω ω' hω h' h => h' (siteSeedReaches_mono _ _ _ _ hω h))
  change (∏ f : FaceIndex, (siteLaw p).real _) ≤ (siteLaw p).real _ at h
  simp_rw [siteQuarterFace_compl_real p 0 m n hmn] at h
  simpa only [Finset.prod_const,Finset.card_univ,card_faceIndex,
    ←Set.compl_iUnion,←siteBoundary_eq_union_reachesFaces] using h

theorem siteQuarterFace_root_bound (p : ℝ) (m n : ℕ) (hmn : m ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    (hseed : (siteLaw p).real (siteSeedInfinite 0 m)ᶜ < ε^24) (c : Vertex) (f : FaceIndex) :
    (siteLaw p).real (siteSeedReaches c m n (QuarterFace c n f))ᶜ < ε := by
  rw [siteQuarterFace_compl_real p c m n hmn]
  apply (pow_lt_pow_iff_left₀ (measureReal_nonneg) hε (by norm_num : (24:ℕ) ≠ 0)).mp
  refine (siteQuarterFace_Harris p m n hmn).trans_lt (lt_of_le_of_lt ?_ hseed)
  exact measureReal_mono (Set.compl_subset_compl.mpr (siteSeedInfinite_subset_reachesBoundary 0 hmn))

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

theorem continuous_parameter : Continuous parameter := by
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem continuous_siteSeedReaches (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    Continuous (fun p => (siteLaw p).real (siteSeedReaches c m n T)) :=
  (ProductCylinder.continuous_probability _ _ (siteSeedReaches_determined c m n hmn T)).comp
    (continuous_pi (fun _ => continuous_parameter))

theorem continuous_siteSeedMiss (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    Continuous (fun p => (siteLaw p).real (siteSeedReaches c m n T)ᶜ) := by
  simp_rw [measureReal_compl (measurableSet_siteSeedReaches c m n hmn T),probReal_univ]
  exact continuous_const.sub (continuous_siteSeedReaches _ _ _ hmn _)

theorem site_lower_quarterFaces {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {m : ℕ} (hseed : (siteLaw p).real (siteSeedInfinite 0 m)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, m ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (siteLaw q).real (siteSeedReaches c m n (QuarterFace c n f)) := by
  obtain ⟨q,hq,hfaces⟩ := exists_lower_forall hp
    (fun n : s => fun t => (siteLaw t).real (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)
    (fun n => continuous_siteSeedMiss _ _ _ (hs n n.property) _) (fun n =>
      (siteQuarterFace_root_bound p m n (hs n n.property) (by positivity) hseed 0 canonicalFace).trans
        (by linarith : γ/2 < γ))
  refine ⟨q,hq,?_⟩
  intro n hn c f
  have h := hfaces ⟨n,hn⟩
  rw [←siteQuarterFace_compl_real q c m n (hs n hn) f,
    measureReal_compl (measurableSet_siteSeedReaches _ _ _ (hs n hn) _),probReal_univ] at h
  linarith

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory Classical
open Filter Topology Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.site_lower_quarterFaces := @_root_.OAI.CriticalZ3.site_lower_quarterFaces
