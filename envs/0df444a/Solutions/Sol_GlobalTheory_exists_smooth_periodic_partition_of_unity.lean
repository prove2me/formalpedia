-- Prove2me | solution 1 for GlobalTheory.exists_smooth_periodic_partition_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:54.853889+00:00
-- url     : https://prove2.me/submissions/9e781737-33ae-4d22-8ec5-4c089828bcaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Theorems.Thm_GlobalTheory_PeriodicPartition_locallyFinite_support_translate
import Theorems.Thm_GlobalTheory_PeriodicPartition_exists_finite_subcover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
namespace GlobalTheory.PeriodicPartition
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
end GlobalTheory.PeriodicPartition
namespace GlobalTheory
open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem hasFiniteSupport_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (z : E) :
    Function.HasFiniteSupport fun l : Λ => φ (z + l) :=
  (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ).point_finite z
open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem contDiff_finsum_of_locallyFinite_support {ι : Type} {f : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hlf : LocallyFinite fun i => Function.support (f i)) :
    ContDiff ℝ ∞ fun x => ∑ᶠ i, f i x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hlf x
  exact (ContDiff.sum fun i _ => hf i).contDiffAt.congr_of_eventuallyEq hs
open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem contDiff_finsum_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ fun z => ∑ᶠ l : Λ, φ (z + l) :=
  contDiff_finsum_of_locallyFinite_support (fun l => hs.comp (contDiff_id.add contDiff_const))
    (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ)
open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem finsum_lattice_translate_add (Λ : Submodule ℤ E) (φ : E → ℝ) (l : Λ) (z : E) :
    ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m) := by
  rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
  simp [add_assoc]
open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem tsupport_finsum_lattice_translate_subset (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (φ : E → ℝ) (hφ : HasCompactSupport φ) (U : Set E) (hU : tsupport φ ⊆ U)
    (hper : ∀ (l : Λ) z, z ∈ U → z + l ∈ U) :
    tsupport (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆ U := by
  have hlf := _root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ
  have h1 : Function.support (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆
      ⋃ l : Λ, Function.support fun z => φ (z + l) := by
    intro z hz
    by_contra h
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at h
    exact hz (by simp [h])
  intro z hz
  have hz' := closure_mono h1 hz
  rw [hlf.closure_iUnion] at hz'
  obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hz'
  have hl' : z + l ∈ tsupport φ := tsupport_comp_subset_preimage φ (continuous_add_right (l : E)) hl
  simpa using hper (-l) _ (hU hl')
end GlobalTheory
end

set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory
open Complex Matrix
open scoped ContDiff BigOperators Real Topology Manifold
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → ∃ (s : Finset ι) (ρ : ι → (Fin g → ℂ) → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧ (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧ ∀ z, ∑ i ∈ s, ρ i z = 1 := by
  intro g Λ hdisc hspan ι U hU hper hcov
  haveI := hdisc
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun x : Fin g → ℂ => {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1})
    (fun x => by
      have hset : {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1} =
          ⋃ l : Λ, (· + (l : Fin g → ℂ)) ⁻¹' Metric.ball x 1 := by
        ext z; simp
      rw [hset]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (continuous_add_right _))
    (fun x l z ⟨m, hm⟩ => ⟨m - l, by
      have hzm : z + (l : Fin g → ℂ) + ((m - l : Λ) : Fin g → ℂ) = z + m := by push_cast; abel
      rw [hzm]
      exact hm⟩)
    (fun z => ⟨z, 0, by simp⟩)
  let β : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun x => ⇑(⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump x)
  let θ : (Fin g → ℂ) → ℝ := fun z => ∑ x ∈ t, β x z
  have hθs : ContDiff ℝ ∞ θ := ContDiff.sum fun x _ => ContDiffBump.contDiff _
  have hθc : HasCompactSupport θ := by
    have hθeq : θ = ∑ x ∈ t, β x := by
      funext z
      simp [θ, Finset.sum_apply]
    rw [hθeq]
    exact HasCompactSupport.finset_sum fun x _ => ContDiffBump.hasCompactSupport _
  have hθn : ∀ z, 0 ≤ θ z := fun z => Finset.sum_nonneg fun x _ => ContDiffBump.nonneg _
  have hθ1 : ∀ x ∈ t, ∀ y ∈ Metric.ball x 1, 1 ≤ θ y := by
    intro x hx y hy
    have h := Finset.single_le_sum (f := fun x => β x y) (fun x _ => ContDiffBump.nonneg _) hx
    have h1 : β x y = 1 := ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hy)
    show 1 ≤ ∑ x ∈ t, β x y
    linarith
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin g → ℂ) isClosed_univ U hU
    (fun z _ => Set.mem_iUnion.2 (hcov z))
  have hps : ∀ i, ContDiff ℝ ∞ (p i) := fun i => contMDiff_iff_contDiff.1 (p i).contMDiff
  have hsfin := p.locallyFinite.finite_nonempty_inter_compact hθc
  let s := hsfin.toFinset
  have hkey : ∀ y, θ y * ∑ i ∈ s, p i y = θ y := by
    intro y
    by_cases hy : θ y = 0
    · simp [hy]
    · have hsum : ∑ᶠ i, p i y = ∑ i ∈ s, p i y := by
        apply finsum_eq_sum_of_support_subset
        intro i hi
        simp only [s, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact ⟨y, hi, subset_tsupport _ hy⟩
      rw [← hsum, p.sum_eq_one (Set.mem_univ y), mul_one]
  let a : ι → (Fin g → ℂ) → ℝ := fun i z => θ z * p i z
  have has : ∀ i, ContDiff ℝ ∞ (a i) := fun i => hθs.mul (hps i)
  have hac : ∀ i, HasCompactSupport (a i) := fun i => hθc.mul_right
  have hat : ∀ i, tsupport (a i) ⊆ U i := fun i => tsupport_mul_subset_right.trans (hp i)
  let Θ : (Fin g → ℂ) → ℝ := fun z => ∑ᶠ l : Λ, θ (z + l)
  have hΘpos : ∀ z, 0 < Θ z := by
    intro z
    obtain ⟨x, hx, l, hl⟩ := ht z
    exact lt_of_lt_of_le one_pos ((hθ1 x hx _ hl).trans
      (single_le_finsum l (hasFiniteSupport_lattice_translate Λ θ hθc z) fun m => hθn _))
  have hΘs : ContDiff ℝ ∞ Θ := contDiff_finsum_lattice_translate Λ θ hθc hθs
  refine ⟨s, fun i z => (∑ᶠ l : Λ, a i (z + l)) / Θ z, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (contDiff_finsum_lattice_translate Λ (a i) (hac i) (has i)).div hΘs fun z => (hΘpos z).ne'
  · intro l z
    simp only [Θ]
    rw [finsum_lattice_translate_add, finsum_lattice_translate_add]
  · show tsupport (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) ⊆ U i
    have hfun : (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) =
        fun z => (∑ᶠ l : Λ, a i (z + l)) * (Θ z)⁻¹ := by
      ext z; rw [div_eq_mul_inv]
    rw [hfun]
    exact tsupport_mul_subset_left.trans
      (tsupport_finsum_lattice_translate_subset Λ (a i) (hac i) (U i) (hat i) (hper i))
  · intro z
    show ∑ i ∈ s, (∑ᶠ l : Λ, a i (z + l)) / Θ z = 1
    rw [← Finset.sum_div, div_eq_one_iff_eq (hΘpos z).ne',
      ← finsum_sum_comm s (fun (l : Λ) i => a i (z + l))
        (fun i _ => hasFiniteSupport_lattice_translate Λ (a i) (hac i) z)]
    apply finsum_congr
    intro l
    simp only [a]
    rw [← Finset.mul_sum]
    exact hkey _
end _root_.GlobalTheory
end GlobalTheory
