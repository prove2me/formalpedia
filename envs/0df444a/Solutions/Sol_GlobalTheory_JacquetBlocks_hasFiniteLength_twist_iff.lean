-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:15.248972+00:00
-- url     : https://prove2.me/submissions/de27744e-9c79-490c-b294-a5c8efaa2cf1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution (ρ : Representation F G V) (χ : G →* Fˣ) :
    HasFiniteLength (twist ρ χ) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.apply_mem_toSubmodule g hv
        rw [twist_apply] at h1
        have h2 := S.toSubmodule.smul_mem ((χ g : F)⁻¹) h1
        rwa [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩
end GlobalTheory.JacquetBlocks
