-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FibreDensityLimit.exists_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:04.457385+00:00
-- url     : https://prove2.me/submissions/c4cec757-f6ae-4d2c-8b79-1b04cc3fdfed

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Topology
open scoped ENNReal NNReal
noncomputable section
namespace GlobalTheory.CompanionTheory.FibreDensityLimit
open Set
private lemma exists_continuous_compactSupport_eq_one_on_compact {V : Type} [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : V → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) ∧ ∀ v ∈ K, ψ v = 1 := by
  obtain ⟨L, -, hLc, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨φ, hφ1, hφ0, hφs, hφb⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  refine ⟨φ, φ.continuous, hφs, ?_, fun v => hφb v, fun v hv => hφ1 hv⟩
  refine (closure_minimal ?_ hLc).trans hLU
  intro v hv
  by_contra hvL
  exact hv (hφ0 (fun hi => hvL (interior_subset hi)))
section Family
variable {V X Y : Type} [MeasurableSpace V] [TopologicalSpace V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {U : Set V} {fib : X → Measure V}
end Family
end GlobalTheory.CompanionTheory.FibreDensityLimit
end
end

set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibreDensityLimit
open Set
namespace GlobalTheory.CompanionTheory.FibreDensityLimit
theorem _root_.solution {V : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] {U : Set V} (hU : IsOpen U) :
    ∃ χ : ℕ → V → ℝ, (∀ n, Continuous (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n, tsupport (χ n) ⊆ U) ∧ (∀ n v, 0 ≤ χ n v ∧ χ n v ≤ 1) ∧
      (∀ v, Monotone fun n => χ n v) ∧ ∀ v ∈ U, ∃ n, χ n v = 1 := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let Kn : ℕ → Set V := fun n => Subtype.val '' compactCovering U n
  have hKc : ∀ n, IsCompact (Kn n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, Kn n ⊆ U := by
    rintro n _ ⟨x, -, rfl⟩
    exact x.2
  have hcov : ∀ v ∈ U, ∃ n, v ∈ Kn n := by
    intro v hv
    have hmem : (⟨v, hv⟩ : U) ∈ ⋃ n, compactCovering U n := by
      rw [iUnion_compactCovering]
      trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact ⟨n, ⟨v, hv⟩, hn, rfl⟩
  choose ψ hψc hψs hψU hψb hψ1 using fun n => exists_continuous_compactSupport_eq_one_on_compact (hKc n) hU (hKU n)
  have hsup : ∀ a b : V → ℝ, HasCompactSupport a → HasCompactSupport b →
      tsupport (a ⊔ b) ⊆ tsupport a ∪ tsupport b := by
    intro a b _ _
    refine closure_minimal ?_ ((isClosed_tsupport a).union (isClosed_tsupport b))
    intro v hv
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    apply hv
    simp [image_eq_zero_of_notMem_tsupport hc.1, image_eq_zero_of_notMem_tsupport hc.2]
  have hP : ∀ n, Continuous (partialSups ψ n) ∧ HasCompactSupport (partialSups ψ n) ∧
      tsupport (partialSups ψ n) ⊆ U ∧ ∀ v, 0 ≤ partialSups ψ n v ∧ partialSups ψ n v ≤ 1 := by
    intro n
    induction n with
    | zero =>
      rw [partialSups_zero]
      exact ⟨hψc 0, hψs 0, hψU 0, hψb 0⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hs : partialSups ψ (n + 1) = partialSups ψ n ⊔ ψ (n + 1) := partialSups_succ ψ n
      rw [hs]
      refine ⟨h1.sup (hψc (n + 1)), ?_, ?_, fun v => ?_⟩
      · exact (h2.union (hψs (n + 1))).of_isClosed_subset (isClosed_tsupport _)
          (hsup _ _ h2 (hψs (n + 1)))
      · exact (hsup _ _ h2 (hψs (n + 1))).trans (Set.union_subset h3 (hψU (n + 1)))
      · exact ⟨le_sup_of_le_left (h4 v).1, sup_le (h4 v).2 (hψb (n + 1) v).2⟩
  refine ⟨fun n => partialSups ψ n, fun n => (hP n).1, fun n => (hP n).2.1, fun n => (hP n).2.2.1,
    fun n => (hP n).2.2.2, fun v m n hmn => (partialSups ψ).monotone hmn v, fun v hv => ?_⟩
  obtain ⟨n, hn⟩ := hcov v hv
  refine ⟨n, le_antisymm ((hP n).2.2.2 v).2 ?_⟩
  rw [← hψ1 n v hn]
  exact le_partialSups ψ n v
end GlobalTheory.CompanionTheory.FibreDensityLimit
