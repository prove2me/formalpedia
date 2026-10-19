-- Prove2me | solution 2 for OAI.PlanarBoundary.blocked_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:31:14.266077+00:00
-- url     : https://prove2.me/submissions/285d1853-2b15-4ae8-bf1f-520d84110c6d

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Peierls.lean:L20-L64
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.blocked_bound. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Theorems.Thm_OAI_GreedyPacking_exists_packing
import Theorems.Thm_OAI_PlanarBoundary_boundary_degree

-- ---- from OAI.Probability.CriticalZ3.Matching ----
namespace OAI

universe uAlpha uE uV

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Exact greedy constants used in the shell trials and contour estimate. -/
namespace GreedyPacking
open Classical

variable {α : Type uAlpha}

end GreedyPacking

namespace FiniteMatching
open Classical
variable {E : Type uE} {V : Type uV} [Fintype E]

omit [Fintype E] in
theorem conflict_refl (a b : E → V) (e : E) : conflict a b e e := Or.inl rfl

omit [Fintype E] in
theorem conflict_symm (a b : E → V) {e f : E} : conflict a b e f → conflict a b f e := by
  unfold conflict
  aesop

theorem conflict_card (a b : E → V)
    (hdeg : ∀ v, (incident a b v).card ≤ 4) (e : E) :
    (Finset.univ.filter (conflict a b e)).card ≤ 7 := by
  have heq : Finset.univ.filter (conflict a b e) = incident a b (a e) ∪ incident a b (b e) := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,incident,conflict,
      Finset.mem_filter,Finset.mem_univ,true_and]
    aesop
  rw [heq]
  have hi : e ∈ incident a b (a e) ∩ incident a b (b e) := by simp [incident]
  have hpos := Finset.card_pos.mpr ⟨e,hi⟩
  have he := Finset.card_union_add_card_inter (incident a b (a e)) (incident a b (b e))
  have ha := hdeg (a e)
  have hb := hdeg (b e)
  omega

theorem exists_matching (a b : E → V) (hdeg : ∀ v, (incident a b v).card ≤ 4) :
    ∃ s : Finset E, (s : Set E).Pairwise (fun e f => ¬conflict a b e f) ∧
      Fintype.card E ≤ 7*s.card := by
  obtain ⟨s,_,hp,hc⟩ := GreedyPacking.exists_packing Finset.univ (conflict a b)
    (fun e _ => conflict_refl a b e) (fun _ _ _ _ => conflict_symm a b)
    7 (fun e _ => conflict_card a b hdeg e)
  exact ⟨s,hp,by simpa only [Finset.card_univ] using hc⟩

/- Choosing either endpoint of each edge of a matching gives distinct vertices. -/
omit [Fintype E] in
theorem endpoint_injective (a b : E → V) (s : Finset E)
    (hp : (s : Set E).Pairwise (fun e f => ¬conflict a b e f)) (choice : s → Bool) :
    Function.Injective (fun e : s => if choice e then a e.val else b e.val) := by
  intro e f hef
  by_contra hne
  have hn : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hc := hp e.property f.property hn
  cases he : choice e <;> cases hf : choice f <;> simp only [he,hf,Bool.false_eq_true,
    ite_false,ite_true] at hef
  · exact hc (Or.inr (Or.inr (Or.inr hef)))
  · exact hc (Or.inr (Or.inr (Or.inl hef)))
  · exact hc (Or.inr (Or.inl hef))
  · exact hc (Or.inl hef)

end FiniteMatching

namespace PlanarBoundary
open Classical

theorem code_degree {n : ℕ} (c : Code n) (hc : Valid c) (v : Point) :
    (FiniteMatching.incident (inner c) (outer c) v).card ≤ 4 := by
  obtain ⟨X,e,hinj,he⟩ := hc
  let f : {i : Fin n // inner c i = v ∨ outer c i = v} →
      {e : Boundary X // primalInside e = v ∨ primalOutside e = v} := fun i =>
    ⟨e i.val,by simpa only [primalInside,primalOutside,inner,outer,he] using i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hij)
  have hh := (Fintype.card_le_of_injective f hf).trans (boundary_degree X v)
  have heq : (FiniteMatching.incident (inner c) (outer c) v).card =
      Fintype.card {i : Fin n // inner c i = v ∨ outer c i = v} := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext i
    simp only [FiniteMatching.incident, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq]
  exact hh

theorem exists_code_matching {n : ℕ} (c : Code n) (hc : Valid c) :
    ∃ s : Finset (Fin n),
      (s : Set (Fin n)).Pairwise (fun i j => ¬FiniteMatching.conflict (inner c) (outer c) i j) ∧
      n ≤ 7*s.card := by
  simpa only [Fintype.card_fin] using FiniteMatching.exists_matching _ _ (code_degree c hc)

end PlanarBoundary

end OAI

-- ---- from OAI.Probability.CriticalZ3.Peierls ----
namespace OAI

universe uOmega

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Matching and endpoint union bound; the bad vertices may be arbitrarily dependent. -/
theorem blocked_bound {n : ℕ} (Bad : Point → Set Ω) (c : Code n) (hc : Valid c)
    {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) :
    μ.real (blocked Bad c) ≤ (2*f)^((n : ℝ)/7) := by
  obtain ⟨s,hpair,hsize⟩ := exists_code_matching c hc
  let choose (η : s → Bool) (i : s) := if η i then inner c i.val else outer c i.val
  let E (η : s → Bool) : Set Ω := {ω | ∀ i : s, ω ∈ Bad (choose η i)}
  have hE (η : s → Bool) : μ.real (E η) ≤ f^s.card := by
    let t : Finset Point := Finset.univ.image (choose η)
    have hinj : Function.Injective (choose η) :=
      FiniteMatching.endpoint_injective _ _ s hpair η
    have ht : t.card = s.card := by
      rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe]
    have he : E η = {ω | ∀ v ∈ t, ω ∈ Bad v} := by
      ext ω
      constructor
      · intro h v hv
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
        exact h i
      · intro h i
        exact h _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [he,←ht]
    exact hbad t
  have hcover : blocked Bad c ⊆ ⋃ η, E η := by
    intro ω hω
    let η : s → Bool := fun i => if ω ∈ Bad (inner c i.val) then true else false
    refine Set.mem_iUnion.mpr ⟨η,?_⟩
    intro i
    by_cases hi : ω ∈ Bad (inner c i.val)
    · simp only [choose,η,hi,ite_true]
    · simpa only [choose,η,hi,ite_false,Bool.false_eq_true] using (hω i.val).resolve_left hi
  have hbound : μ.real (blocked Bad c) ≤ (2*f)^s.card := by
    calc
      _ ≤ μ.real (⋃ η, E η) := measureReal_mono hcover
      _ ≤ ∑ η, μ.real (E η) := measureReal_iUnion_fintype_le E
      _ ≤ ∑ _η : s → Bool, f^s.card := Finset.sum_le_sum (fun η _ => hE η)
      _ = (2*f)^s.card := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
          Fintype.card_coe,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow]
  apply hbound.trans
  rw [←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_ge (by positivity) hf1
  have hs : (n : ℝ) ≤ 7*s.card := by exact_mod_cast hsize
  linarith

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Filter Topology
open Classical _root_.MeasureTheory ProbabilityTheory


theorem solution.{uOmega} : type_of% @_root_.OAI.PlanarBoundary.blocked_bound.{uOmega} := @_root_.OAI.PlanarBoundary.blocked_bound.{uOmega}
