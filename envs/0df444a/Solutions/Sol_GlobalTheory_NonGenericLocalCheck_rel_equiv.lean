-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.rel_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:54.931118+00:00
-- url     : https://prove2.me/submissions/7cf527be-4bfb-485f-907c-cc2c6e00df3a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_framePairFixator_unitary_and_fixes_frame
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_perp_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution (P : FPair H r) : Equivalence (Datum.Rel (P := P)) where
  refl d := ⟨1, P.UW0.one_mem, by
    refine ⟨fun x y h => ?_, fun x y h => ?_, fun x' y' x y h' h => ?_⟩
    · rw [show y = x from Subtype.ext h]
    · rw [show y = x from Subtype.ext h]
    · rw [show y' = x' from Subtype.ext h', show y = x from Subtype.ext h]⟩
  symm := by
    rintro d d' ⟨g, hg, h1, h2, h3⟩
    refine ⟨g⁻¹, P.UW0.inv_mem hg, fun x y hxy => ?_, fun x y hxy => ?_,
      fun x' y' x y hx' hx => ?_⟩
    · have e : (x : V) = g y := by rw [hxy]; exact (g.apply_symm_apply (x : V)).symm
      exact (h1 y x e).symm
    · have e : (x : V) = g y := by rw [hxy]; exact (g.apply_symm_apply (x : V)).symm
      exact (h2 y x e).symm
    · have e1 : (x' : V) = g y' := by rw [hx']; exact (g.apply_symm_apply (x' : V)).symm
      have e2 : (x : V) = g y := by rw [hx]; exact (g.apply_symm_apply (x : V)).symm
      exact (h3 y' x' y x e1 e2).symm
  trans := by
    rintro d d' d'' ⟨g, hg, h1, h2, h3⟩ ⟨g', hg', k1, k2, k3⟩
    have sA : ∀ u : ↥(H.perp (H.X P.A.f)), g u ∈ H.perp (H.X P.A.f) := fun u =>
      perp_stable (framePairFixator_unitary_and_fixes_frame P hg).1 P.A.f (fun b => ((framePairFixator_unitary_and_fixes_frame P hg).2 b).1) u.2
    have sB : ∀ u : ↥(H.perp (H.X P.B.f)), g u ∈ H.perp (H.X P.B.f) := fun u =>
      perp_stable (framePairFixator_unitary_and_fixes_frame P hg).1 P.B.f (fun b => ((framePairFixator_unitary_and_fixes_frame P hg).2 b).2) u.2
    refine ⟨g' * g, P.UW0.mul_mem hg' hg, fun x z hz => ?_, fun x z hz => ?_,
      fun x' z' x z hz' hz => ?_⟩
    · exact (h1 x ⟨g x, sA x⟩ rfl).trans (k1 ⟨g x, sA x⟩ z hz)
    · exact (h2 x ⟨g x, sB x⟩ rfl).trans (k2 ⟨g x, sB x⟩ z hz)
    · exact (h3 x' ⟨g x', sB x'⟩ x ⟨g x, sA x⟩ rfl rfl).trans (k3 ⟨g x', sB x'⟩ z' ⟨g x, sA x⟩ z hz' hz)
end GlobalTheory.NonGenericLocalCheck
