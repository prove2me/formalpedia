-- Prove2me | solution 1 for GlobalTheory.Mass.ProdMass.orbMass_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:53.068167+00:00
-- url     : https://prove2.me/submissions/24bb48b2-9506-4f3e-9d03-942105233d31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul
import Theorems.Thm_GlobalTheory_Mass_ProdMass_orbMass_eq
import Theorems.Thm_GlobalTheory_Mass_ProdMass_wt_rel
import Theorems.Thm_GlobalTheory_Mass_ProdMass_wt_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ProdMass
variable {Γ G G' α β : Type} [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β]
  [MulAction Γ (α × β)] (φ : Γ ≃* G × G')
  (hφ : ∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2))
namespace GlobalTheory.Mass.ProdMass
theorem _root_.solution : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α]
    [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β),
    (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y →
    (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) →
    orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by
  intro Γ G G' α β _ _ _ _ _ _ φ X Y hφ hX hY _ _
  have hXY : Stable Γ (X ×ˢ Y) := by
    intro γ p hp
    rw [hφ]
    exact ⟨hX _ _ hp.1, hY _ _ hp.2⟩
  rw [orbMass_eq, orbMass_eq, orbMass_eq, ← (orbEquiv φ hφ).symm.tsum_eq, ENNReal.tsum_prod',
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [← wt_prod φ hφ X Y (Quotient.out a, Quotient.out b)]
  exact wt_rel Γ _ hXY (Quotient.mk_out (s := MulAction.orbitRel Γ (α × β)) _)
end GlobalTheory.Mass.ProdMass
