-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.LatSum.tile_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:53.264784+00:00
-- url     : https://prove2.me/submissions/d7355c0c-dc12-4cf0-9590-d3a9c235f07b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScalingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegersStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedeanStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeCosetScaledRiemannSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.LatSum
variable {A O Q ι : Type} [AddCommGroup A] [AddCommGroup O] [Fintype ι] [Fintype Q]
namespace GlobalTheory.CompanionTheory.Equi.LatSum
theorem _root_.solution (H : AddSubgroup O) (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) (hq : ∀ a b, q a = q b ↔ a - b ∈ H) (D₀ : Set A)
    (hD : ∀ y : A, ∃! a : O, y - j a ∈ D₀) (y : ι → A) :
    ∃! p : (ι → A) × (ι → A), p.1 ∈ reps (ι := ι) j rep ∧
      p.2 ∈ AddSubgroup.pi Set.univ (fun _ : ι => H.map j) ∧
      y - p.1 - p.2 ∈ Set.pi Set.univ (fun _ : ι => D₀) := by
  choose a ha hau using fun i => hD (y i)
  refine ⟨(fun i => j (rep (q (a i))), fun i => j (a i - rep (q (a i)))), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.2 ⟨fun i => q (a i), Finset.mem_univ _, rfl⟩
  · intro i _
    refine AddSubgroup.mem_map.2 ⟨a i - rep (q (a i)), ?_, rfl⟩
    exact (hq _ _).1 (hrep _).symm
  · intro i _
    have : y i - j (rep (q (a i))) - j (a i - rep (q (a i))) = y i - j (a i) := by
      rw [map_sub]; abel
    simpa [this] using ha i
  · rintro ⟨p₁, p₂⟩ ⟨h1, h2, h3⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
    have hl : ∀ i, ∃ l ∈ H, j l = p₂ i := fun i => by
      obtain ⟨l, hl, e⟩ := AddSubgroup.mem_map.1 (h2 i (Set.mem_univ i))
      exact ⟨l, hl, e⟩
    choose l hlH hlj using hl
    have hai : ∀ i, rep (c i) + l i = a i := fun i => by
      refine hau i _ ?_
      have h4 := h3 i (Set.mem_univ i)
      have h5 : y i - j (rep (c i) + l i) = (y - (fun i => j (rep (c i))) - p₂) i := by
        simp only [Pi.sub_apply, map_add, hlj]; abel
      show y i - j (rep (c i) + l i) ∈ D₀
      rw [h5]; exact h4
    have hc : ∀ i, q (a i) = c i := fun i => by
      have h6 : q (a i) = q (rep (c i)) := (hq _ _).2 (by rw [← hai i]; simpa using hlH i)
      rwa [hrep] at h6
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show j (rep (c i)) = j (rep (q (a i)))
      rw [hc]
    · show p₂ i = j (a i - rep (q (a i)))
      rw [hc, ← hai i, add_sub_cancel_left, hlj]
end GlobalTheory.CompanionTheory.Equi.LatSum
