-- Prove2me | solution 1 for GlobalTheory.LatHecke.heckeAll_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:26.127423+00:00
-- url     : https://prove2.me/submissions/f67d0cb5-ce30-48c3-a30a-951452d1b41e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Theorems.Thm_GlobalTheory_LatHecke_smul_mem_subIdx_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatHecke
open scoped TensorProduct
variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
variable [IsFractionRing O K] (r : ℕ)
variable {O K r}
variable [Finite (IsLocalRing.ResidueField O)]
variable {E : Type} [AddCommMonoid E]
namespace GlobalTheory.LatHecke
theorem _root_.solution (g : GL (Fin r) K) (n : ℕ) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeAll n φ (g • L) = heckeAll n (fun M => φ (g • M)) L := by
  symm
  refine finsum_mem_eq_of_bijOn (fun M => g • M) ⟨fun M hM => (smul_mem_subIdx_iff g n M L).2 hM,
    (MulAction.injective g).injOn, fun M hM => ⟨g⁻¹ • M, ?_, smul_inv_smul g M⟩⟩ fun _ _ => rfl
  rw [← smul_mem_subIdx_iff g, smul_inv_smul]; exact hM
end GlobalTheory.LatHecke
