-- Prove2me | solution 1 for GlobalTheory.LatBasis.exists_basis_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:22.13487+00:00
-- url     : https://prove2.me/submissions/b2d8edb3-bd9d-4676-80f0-bce92530ea23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Theorems.Thm_GlobalTheory_LatDen_latDen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.LatBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LatBasis
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (W : Submodule E (Fin r → E)), ∃ w : Fin (Module.finrank E W) → Fin r → E, LinearIndependent E w ∧ (∀ a, w a ∈ X.Λ) ∧ Submodule.span E (Set.range w) = W) := by
  intro r X W
  choose n hn hmem using (GlobalTheory.LatDen.latDen r X).1
  set b := Module.finBasis E W
  set v : Fin (Module.finrank E W) → Fin r → E := fun i => (b i : Fin r → E) with hv
  have hvli : LinearIndependent E v := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hne : ∀ i, (n (v i) : E) ≠ 0 := fun i => Nat.cast_ne_zero.2 (hn (v i)).ne'
  set c : Fin (Module.finrank E W) → Eˣ := fun i => Units.mk0 _ (hne i)
  have hli : LinearIndependent E (fun i => (n (v i) : E) • v i) := hvli.units_smul c
  refine ⟨fun i => (n (v i) : E) • v i, hli, fun a => hmem (v a), ?_⟩
  have hle : Submodule.span E (Set.range fun i => (n (v i) : E) • v i) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact W.smul_mem _ (b i).2
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, Fintype.card_fin]
end GlobalTheory.LatBasis
