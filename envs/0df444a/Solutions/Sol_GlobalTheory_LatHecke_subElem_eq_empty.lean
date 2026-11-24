-- Prove2me | solution 1 for GlobalTheory.LatHecke.subElem_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:21.754047+00:00
-- url     : https://prove2.me/submissions/16446fb5-9c5f-4fb1-a7bc-9c06914d39f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt

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
namespace GlobalTheory.LatHecke
theorem _root_.solution {k : ℕ} (hk : r < k)
    (L : Lat O K r) : subElem k L = ∅ := by
  ext M
  simp only [subElem, subIdx, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, h3⟩
  have h := AddSubgroup.relIndex_mul_relIndex (maxMul L).1.toAddSubgroup M.1.toAddSubgroup
      L.1.toAddSubgroup h3 h1
  rw [h2, relIndex_maxMul] at h
  have hd : qRes O ^ k ∣ qRes O ^ r := Dvd.intro_left _ h
  have := (Nat.pow_dvd_pow_iff_le_right (two_le_qRes (O := O))).1 hd
  omega
end GlobalTheory.LatHecke
