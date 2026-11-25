-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData.isInnerLattice_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:08.820105+00:00
-- url     : https://prove2.me/submissions/1af1768a-f585-4659-9370-9831aac58ea7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_FrameCoefficientData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
variable {o F E V : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
  [Field F] [Algebra o F] [IsFractionRing o F]
  [CommRing E] [StarRing E] [Algebra F E] [Algebra o E]
  [AddCommGroup V] [Module E V] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
theorem _root_.solution (n : ℕ) (A : Frame F (Fin n → E) 0) (i₀ : Fin n)
    (hz : ∀ i, A.z i ∈ MaxOrd o E) (h1 : A.z i₀ = 1)
    (hs : ∀ x ∈ MaxOrd o E, star x ∈ MaxOrd o E) :
    A.IsInnerLattice (negStd E n)
      (Submodule.span (MaxOrd o E) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))) := by
  classical
  have hX : A.X E 0 = ⊥ := by simp [Frame.X]
  have hm : ∀ v : Fin n → E, v ∈ Submodule.span (MaxOrd o E)
      (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E)) ↔ ∀ i, v i ∈ MaxOrd o E := by
    intro v
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩ i
      simp [Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]
    · intro hv
      refine ⟨fun i => ⟨v i, hv i⟩, ?_⟩
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]
  refine ⟨⟨Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E), by simp [hX]⟩,
    fun v => ?_, (hm _).2 hz, fun c hc => by simpa [h1] using (hm _).1 hc i₀⟩
  constructor
  · intro hv
    refine ⟨fun w hw => by simp [hX] at hw; simp [hw], fun w hw => ?_⟩
    exact (MaxOrd o E).neg_mem ((MaxOrd o E).sum_mem fun i _ =>
      (MaxOrd o E).mul_mem ((hm _).1 hv i) (hs _ ((hm _).1 hw i)))
  · rintro ⟨-, hv⟩
    refine (hm _).2 fun i => ?_
    have := hv (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩)
    simpa [negStd, Pi.single_apply, apply_ite (star : E → E)] using this
end GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
