-- Prove2me | solution 1 for GlobalTheory.RowFubini.cross_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:38:36.490892+00:00
-- url     : https://prove2.me/submissions/e410cf42-3117-44ee-93be-c2b964cb0579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
import Theorems.Thm_GlobalTheory_RowFubini_relIndex_split
import Theorems.Thm_GlobalTheory_RowFubini_measure_eq_relIndex_mul
import Theorems.Thm_GlobalTheory_RowFubini_comap_open_compact
import Theorems.Thm_GlobalTheory_RowFubini_map_open_compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
namespace GlobalTheory.RowFubini
theorem _root_.solution {X Y : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N : Subgroup X) (π : R →* Y) (σ : Y →* R)
    (hR : IsClosed (R : Set X)) (hN : IsClosed (N : Set X)) (hNR : N ≤ R)
    (hπ : Continuous π) (hσ : Continuous σ) (hsec : ∀ y, π (σ y) = y)
    (hker : ∀ r : R, π r = 1 ↔ r.1 ∈ N)
    (ρ : Measure R) [ρ.IsMulLeftInvariant] (la : Measure N) [la.IsMulLeftInvariant]
    (ν : Measure Y) [ν.IsMulLeftInvariant] (Q₁ Q₂ : Subgroup X) (h12 : Q₁ ≤ Q₂)
    (h1o : IsOpen (Q₁ : Set X)) (h1c : IsCompact (Q₁ : Set X))
    (h2o : IsOpen (Q₂ : Set X)) (h2c : IsCompact (Q₂ : Set X)) :
    ρ.real (Q₂.comap R.subtype) * la.real (Q₁.comap N.subtype) *
        ν.real ((Q₁.comap R.subtype).map π) =
      ρ.real (Q₁.comap R.subtype) * la.real (Q₂.comap N.subtype) *
        ν.real ((Q₂.comap R.subtype).map π) := by
  obtain ⟨a1o, a1c⟩ := comap_open_compact R Q₁ hR h1o h1c
  obtain ⟨a2o, a2c⟩ := comap_open_compact R Q₂ hR h2o h2c
  obtain ⟨n1o, -⟩ := comap_open_compact N Q₁ hN h1o h1c
  obtain ⟨-, n2c⟩ := comap_open_compact N Q₂ hN h2o h2c
  obtain ⟨p1o, -⟩ := map_open_compact _ π σ hπ hσ hsec a1o a1c
  obtain ⟨-, p2c⟩ := map_open_compact _ π σ hπ hσ hsec a2o a2c
  have hA : Q₁.comap R.subtype ≤ Q₂.comap R.subtype := Subgroup.comap_mono h12
  have ea := measure_eq_relIndex_mul ρ _ _ hA a1o a2c
  have en := measure_eq_relIndex_mul la _ _ (Subgroup.comap_mono h12) n1o n2c
  have ep := measure_eq_relIndex_mul ν _ _ (Subgroup.map_mono hA) p1o p2c
  have hmap : (Q₂.comap N.subtype).map (Subgroup.inclusion hNR) = Q₂.comap R.subtype ⊓ π.ker := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨hn, (hker _).2 n.2⟩
    · rintro ⟨hq, hk⟩
      exact ⟨⟨r.1, (hker r).1 hk⟩, hq, rfl⟩
  have hidx : (Q₁.comap R.subtype).relIndex (Q₂.comap R.subtype ⊓ π.ker) =
      (Q₁.comap N.subtype).relIndex (Q₂.comap N.subtype) := by
    rw [← hmap, ← Subgroup.relIndex_comap]
    rfl
  have hs := relIndex_split π _ _ hA
  rw [hidx] at hs
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  rw [ea, en, ep, hs]
  congr 1
  push_cast
  ring
end GlobalTheory.RowFubini
