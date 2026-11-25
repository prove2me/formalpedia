-- Prove2me | solution 1 for GlobalTheory.PDivGroup.natCard_ker_ptsMap_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:52:12.054595+00:00
-- url     : https://prove2.me/submissions/d5085d06-eca8-4834-b4d1-0a55cd69e6d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDivGroup_ptsMap_res_mulP
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable {B : Type} [CommRing B] [Algebra O B]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) :
    Nat.card (pointsMap O (G.mulP n)).ker = Nat.card (G.A 1 →ₐ[O] O) := by
  obtain ⟨f, hf, hk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  have key : ∀ x : WithConv (G.A (n + 1) →ₐ[O] O),
      x ∈ (pointsMap O (G.mulP n)).ker ↔ RingHom.ker f ≤ RingHom.ker x.ofConv := fun x => by
    rw [hk, torsionIdeal_le_ker_iff, pow_one, toConv_ofConv, ← ptsMap_res_mulP,
      map_eq_one_iff _ (G.ptsMap_res_injective n), MonoidHom.mem_ker]
  have hm : ∀ y : G.A 1 →ₐ[O] O, toConv (y.comp (f : G.A (n + 1) →ₐ[O] G.A 1)) ∈
      (pointsMap O (G.mulP n)).ker := fun y => (key _).2 fun a ha => by
    have ha' : f a = 0 := ha
    change y (f a) = 0
    rw [ha', map_zero]
  refine (Nat.card_congr (Equiv.ofBijective (fun y => ⟨_, hm y⟩)
    ⟨fun y z h => AlgHom.ext fun a => ?_, fun x => ?_⟩)).symm
  · obtain ⟨b, rfl⟩ := hf a
    exact DFunLike.congr_fun (congrArg ofConv (congrArg Subtype.val h)) b
  · have h1 := AlgHom.liftOfSurjective_comp (f : G.A (n + 1) →ₐ[O] G.A 1) hf x.1.ofConv
      ((key x.1).1 x.2)
    exact ⟨_, Subtype.ext (ofConv_injective h1)⟩
end GlobalTheory.PDivGroup
