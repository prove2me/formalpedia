-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.perp_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:25.871422+00:00
-- url     : https://prove2.me/submissions/b4fce456-b477-4570-8cd7-6d256d6ab369

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame

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
theorem _root_.solution {g : V ≃ₗ[E] V} (hu : IsUnitary H g) (f : Fin (r + 1) → V)
    (hf : ∀ b, g (f b) = f b) {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  have hfix : H.X f ≤ LinearMap.eqLocus (g : V →ₗ[E] V) LinearMap.id := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_eqLocus.mpr (hf _)
  have hv' : ∀ x ∈ H.X f, H.h v x = 0 := hv
  have hu' : ∀ x y, H.h (g x) (g y) = H.h x y := hu
  show ∀ x ∈ H.X f, H.h (g v) x = 0
  intro x hx
  have hx' : g x = x := LinearMap.mem_eqLocus.mp (hfix hx)
  rw [← hx', hu']
  exact hv' x hx
end GlobalTheory.NonGenericLocalCheck
