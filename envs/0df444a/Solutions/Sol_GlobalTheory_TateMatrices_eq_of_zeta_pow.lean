-- Prove2me | solution 1 for GlobalTheory.TateMatrices.eq_of_zeta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:51:21.977464+00:00
-- url     : https://prove2.me/submissions/aefeb29a-1527-476d-ad06-539204898d6e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.TateMatrices
theorem _root_.solution {G : Type} [CommGroup G] {κ : Type} [Fintype κ] (ζ : ℕ → G)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (p ^ (n + 1))) (a b c d : κ → ℤ_[p])
    (h : ∀ n, ζ n ^ (∑ k, (PadicInt.toZModPow (n + 1) (a k)).val * (PadicInt.toZModPow (n + 1) (b k)).val) =
      ζ n ^ (∑ k, (PadicInt.toZModPow (n + 1) (c k)).val * (PadicInt.toZModPow (n + 1) (d k)).val)) :
    ∑ k, a k * b k = ∑ k, c k * d k := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rcases n with _ | n
  · haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  · have h1 := h n
    rw [pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf, ← ZMod.natCast_eq_natCast_iff] at h1
    simpa using h1
end GlobalTheory.TateMatrices
