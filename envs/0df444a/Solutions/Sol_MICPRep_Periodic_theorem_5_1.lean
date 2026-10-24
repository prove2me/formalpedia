-- Prove2me | solution 1 for MICPRep.Periodic.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:11:38.859735+00:00
-- url     : https://prove2.me/submissions/e339b34f-1b34-4af8-b8dd-f8ad12a303c6

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting
import Theorems.Thm_MICPRep_Periodic_proposition_4_2
import Theorems.Thm_MICPRep_Periodic_proposition_6_1

open MICPRep.Periodic
open scoped ENNReal Matrix

set_option linter.unusedVariables false in
def CoverStatement : Prop :=
  ∀ {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hD : micpDiam M < ⊤),
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (T : Fin k → Set (Pt n)),
        (∀ i, HasNearlyPeriodicFormulation (T i)) ∧
        S ⊆ S₀ ∪ ⋃ i, T i ∧ S₀ ∪ ⋃ i, T i ⊆ closure S

namespace MICPRep.Periodic.MainCover

open scoped ENNReal Matrix

lemma fiber_convex {n p d : ℕ} {M : Set (Ambient n p d)}
    (hM : Convex ℝ M) (z : Fin d → ℝ) : Convex ℝ (zProj M z) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨v, hv⟩ := hx
  obtain ⟨w, hw⟩ := hy
  refine ⟨a • v + b • w, ?_⟩
  have h := hM hv hw ha hb hab
  have hz : a • z + b • z = z := by rw [← add_smul, hab, one_smul]
  simpa only [Prod.smul_mk, Prod.mk_add_mk, hz] using h

lemma fiber_subset {n p d : ℕ} {M : Set (Ambient n p d)} {S : Set (Pt n)}
    (hM : Induces M S) {z : Fin d → ℝ} (hz : z ∈ intLattice d) :
    zProj M z ⊆ S := by
  rintro x ⟨y, hy⟩
  exact (hM.2.2 x).mpr ⟨y, z, hz, hy⟩

lemma finite_diameter {n p d : ℕ} {M : Set (Ambient n p d)} {S : Set (Pt n)}
    (hM : Induces M S)
    (hdiam : ∃ D : ℝ, ∀ C ⊆ S, Convex ℝ C → Metric.ediam C ≤ ENNReal.ofReal D) :
    micpDiam M < ⊤ := by
  obtain ⟨D, hD⟩ := hdiam
  apply lt_of_le_of_lt (show micpDiam M ≤ ENNReal.ofReal D from ?_) ENNReal.ofReal_lt_top
  exact iSup_le fun z => iSup_le fun hz =>
    hD (zProj M z) (fiber_subset hM hz.2) (fiber_convex hM.2.1 z)

lemma lattice_add_nsmul {d : ℕ} {z r : Fin d → ℝ}
    (hz : z ∈ intLattice d) (hr : r ∈ intLattice d) (k : ℕ) :
    z + (k : ℝ) • r ∈ intLattice d := by
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hr
  refine ⟨fun i => a i + (k : ℤ) * b i, ?_⟩
  ext i
  simp

lemma periodic_closure {n : ℕ} {T : Set (Pt n)}
    (hT : HasNearlyPeriodicFormulation T) : IsPeriodic (closure T) := by
  obtain ⟨p, d, M, hM, u, hu, r, hrZ, _hr0, _hrI, hmove⟩ := hT
  refine ⟨u, hu, ?_⟩
  intro x hx k _hk
  have hbase : T ⊆ (fun x : Pt n => x + (k : ℝ) • u) ⁻¹' closure T := by
    intro y hy
    obtain ⟨w, z, hz, hwz⟩ := (hM.2.2 y).mp hy
    have hzI : z ∈ indexSet M := ⟨(y, w, z), hwz, rfl⟩
    exact closure_mono (fiber_subset hM (lattice_add_nsmul hz hrZ k))
      (hmove k z ⟨hz, hzI⟩ y ⟨w, hwz⟩)
  exact closure_minimal hbase (isClosed_closure.preimage (continuous_id.add continuous_const)) hx

end MICPRep.Periodic.MainCover

open MICPRep.Periodic MICPRep.Periodic.MainCover
open scoped ENNReal Matrix

/-- The headline classification follows from the exact finite-cover proposition. -/
theorem conditional_solution (hcover : CoverStatement)
    {n : ℕ} (S : Set (Pt n)) (hclosed : IsClosed S) (hrat : IsRationalMICPR S)
    (hdiam : ∃ D : ℝ, ∀ C ⊆ S, Convex ℝ C → Metric.ediam C ≤ ENNReal.ofReal D) :
    ∃ (k₁ k₂ : ℕ) (C : Fin k₁ → Set (Pt n)) (T : Fin k₂ → Set (Pt n)),
      (∀ j, IsCompact (C j) ∧ Convex ℝ (C j)) ∧
      (∀ i, IsClosed (T i) ∧ IsPeriodic (T i)) ∧
      S = (⋃ j, C j) ∪ (⋃ i, T i) := by
  classical
  obtain ⟨p, d, M, hM⟩ := hrat
  obtain ⟨B, hB, k, T, hT, hlo, hhi⟩ := hcover M S hM (finite_diameter hM.1 hdiam)
  have hBS : B ⊆ S := fun _ hx => hclosed.closure_subset (hhi (Or.inl hx))
  have hTS : ∀ i, T i ⊆ S := fun i _ hx =>
    hclosed.closure_subset (hhi (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)))
  obtain ⟨q, l, St, hSt, hBeq⟩ := (proposition_4_2 B).1.mp hB
  let C : Fin l → Set (Pt n) := fun j => closure (Prod.fst '' St j)
  have hprojS : ∀ j, Prod.fst '' St j ⊆ S := by
    intro j x hx
    apply hBS
    rw [hBeq]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  have hC : ∀ j, IsCompact (C j) ∧ Convex ℝ (C j) := by
    intro j
    have hc : Convex ℝ (Prod.fst '' St j) :=
      (hSt j).2.2.linear_image (LinearMap.fst ℝ (Pt n) (Fin q → ℝ))
    obtain ⟨D, hD⟩ := hdiam
    have hb : Bornology.IsBounded (Prod.fst '' St j) :=
      Metric.isBounded_iff_ediam_ne_top.mpr
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hD _ (hprojS j) hc))
    exact ⟨hb.isCompact_closure, hc.closure⟩
  refine ⟨l, k, C, fun i => closure (T i), hC, ?_, ?_⟩
  · exact fun i => ⟨isClosed_closure, periodic_closure (hT i)⟩
  · apply Set.Subset.antisymm
    · intro x hx
      rcases hlo hx with hx | hx
      · left
        rw [hBeq] at hx
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨j, subset_closure hj⟩
      · right
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
    · intro x hx
      rcases hx with hx | hx
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact closure_minimal (hprojS j) hclosed hj
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact closure_minimal (hTS i) hclosed hi

theorem solution {n : ℕ} (S : Set (Pt n)) (hclosed : IsClosed S) (hrat : IsRationalMICPR S)
    (hdiam : ∃ D : ℝ, ∀ C ⊆ S, Convex ℝ C → Metric.ediam C ≤ ENNReal.ofReal D) :
    ∃ (k₁ k₂ : ℕ) (C : Fin k₁ → Set (Pt n)) (T : Fin k₂ → Set (Pt n)),
      (∀ j, IsCompact (C j) ∧ Convex ℝ (C j)) ∧
      (∀ i, IsClosed (T i) ∧ IsPeriodic (T i)) ∧
      S = (⋃ j, C j) ∪ (⋃ i, T i) := by
  have hcover : CoverStatement := @MICPRep.Periodic.proposition_6_1
  exact conditional_solution hcover S hclosed hrat hdiam
