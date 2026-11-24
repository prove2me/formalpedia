-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.flag_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:50.834802+00:00
-- url     : https://prove2.me/submissions/6ac5d515-f062-4961-a21f-3d9c0e1602f5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.CoordUnip
private lemma flag_iff_lemma {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] (A : ℕ → Submodule E V)
    (h0 : A 0 = ⊥) (hm : ∀ j, A j ≤ A (j + 1)) (r : ℕ) (g : V ≃ₗ[E] V)
    (hg : ∀ j, j < r → ∀ v ∈ A (j + 1), g v - v ∈ A j) :
    ∀ j, j ≤ r → ∀ u ∈ A j, ∃ w ∈ A j, g w = u := by
  intro j
  induction j with
  | zero =>
    intro _ u hu
    rw [h0, Submodule.mem_bot] at hu
    exact ⟨0, by rw [h0]; exact Submodule.zero_mem _, by rw [hu, map_zero]⟩
  | succ i ih =>
    intro hi u hu
    obtain ⟨w, hw, hgw⟩ := ih (by omega) (g u - u) (hg i (by omega) u hu)
    refine ⟨u - w, Submodule.sub_mem _ hu (hm i hw), ?_⟩
    rw [map_sub, hgw]
    abel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
section Frame
variable (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V)
end Frame
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
end GlobalTheory.HL.CoordUnip
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordUnip
namespace GlobalTheory.HL.CoordUnip
theorem _root_.solution {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] (A : ℕ → Submodule E V)
    (h0 : A 0 = ⊥) (hm : ∀ j, A j ≤ A (j + 1)) (r : ℕ) (g : V ≃ₗ[E] V)
    (hg : ∀ j, j < r → ∀ v ∈ A (j + 1), g v - v ∈ A j) :
    ∀ j, j ≤ r → ∀ v, g v ∈ A j ↔ v ∈ A j := by
  intro j hj v
  constructor
  · intro hv
    obtain ⟨w, hw, hgw⟩ := flag_iff_lemma A h0 hm r g hg j hj (g v) hv
    rw [← g.injective hgw]
    exact hw
  · intro hv
    cases j with
    | zero =>
      rw [h0, Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ i =>
      have hd := hg i (by omega) v hv
      have h2 : g v = (g v - v) + v := by abel
      rw [h2]
      exact Submodule.add_mem _ (hm i hd) hv
end GlobalTheory.HL.CoordUnip
