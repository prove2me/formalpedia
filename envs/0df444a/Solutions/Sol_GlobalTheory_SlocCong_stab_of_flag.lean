-- Prove2me | solution 1 for GlobalTheory.SlocCong.stab_of_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:17.159391+00:00
-- url     : https://prove2.me/submissions/38609b84-a9f9-4bf5-9b13-180e2f87fdce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFamiliesCongrModUnitriangular
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S
open GlobalTheory GlobalTheory.SlocCong
namespace GlobalTheory.SlocCong
theorem _root_.solution {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (f : Fin n → V) (g : V →ₗ[E] V)
    (hg : ∀ a, g (f a) - f a ∈ Submodule.span E (f '' {c | c < a})) (a : Fin n) :
    ∀ v ∈ Submodule.span E (f '' {c | c < a}), g v ∈ Submodule.span E (f '' {c | c < a}) := by
  intro v hv
  have : Submodule.span E (f '' {c | c < a}) ≤ (Submodule.span E (f '' {c | c < a})).comap g := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    have h1 : Submodule.span E (f '' {c' | c' < c}) ≤ Submodule.span E (f '' {c | c < a}) :=
      Submodule.span_mono (Set.image_mono fun c' (hc' : c' < c) => (show c' < a from lt_trans hc' hc))
    have h2 : f c ∈ Submodule.span E (f '' {c | c < a}) := Submodule.subset_span ⟨c, hc, rfl⟩
    have := Submodule.add_mem _ (h1 (hg c)) h2
    simpa using this
  exact this hv
end GlobalTheory.SlocCong
