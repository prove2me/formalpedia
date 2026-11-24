-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.finrank_le_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:27.602346+00:00
-- url     : https://prove2.me/submissions/cdedf95c-79ac-4f82-8b07-a7963c2a3c05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
namespace GlobalTheory.UU.SchurComp
theorem _root_.solution {F E Q : Type} [Field F] [AddCommGroup E] [Module F E] [AddCommGroup Q] [Module F Q]
    (W : Submodule F E) (f : E →ₗ[F] Q) (hf : ∀ v ∈ W, f v = 0 → v = 0) {n : ℕ} (b : Fin n → Q)
    (hb : ∀ v, f v ∈ Submodule.span F (Set.range b)) : Module.finrank F W ≤ n ∧
      (n ≤ Module.finrank F W → ∀ q ∈ Submodule.span F (Set.range b), ∃ v ∈ W, f v = q) := by
  haveI : FiniteDimensional F (Submodule.span F (Set.range b)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range b)
  have h1 : Module.finrank F (Submodule.span F (Set.range b)) ≤ n :=
    (finrank_range_le_card b).trans (Fintype.card_fin n).le
  have hi : Function.Injective (f.domRestrict W) :=
    (injective_iff_map_eq_zero _).2 fun v hv => Subtype.ext (hf v.1 v.2 hv)
  have h2 := LinearMap.finrank_range_of_inj hi
  have hle : LinearMap.range (f.domRestrict W) ≤ Submodule.span F (Set.range b) := by
    rintro _ ⟨v, rfl⟩; exact hb v.1
  refine ⟨h2 ▸ (Submodule.finrank_mono hle).trans h1, fun hn q hq => ?_⟩
  rw [← Submodule.eq_of_le_of_finrank_le hle (h1.trans (h2 ▸ hn))] at hq
  obtain ⟨v, hv⟩ := hq
  exact ⟨v.1, v.2, hv⟩
end GlobalTheory.UU.SchurComp
