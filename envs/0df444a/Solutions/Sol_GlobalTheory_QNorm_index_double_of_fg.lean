-- Prove2me | solution 1 for GlobalTheory.QNorm.index_double_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:57:41.696842+00:00
-- url     : https://prove2.me/submissions/2ed47ca2-b81a-4f56-833c-e2d3bb562905

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFg
import Theorems.Thm_GlobalTheory_QNorm_index_double_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (M : Type) [AddCommGroup M] [AddGroup.FG M] :
    (nsmulAddMonoidHom (α := M) 2).range.index =
      2 ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ (DFinsupp.equivFunOnFintype).symm
  have h := index_double_prod (Fin n →₀ ℤ) (DirectSum ι fun i => ZMod (p i ^ e i))
  rw [← AddSubgroup.index_map_equiv _ f, AddEquiv.map_range_nsmulAddMonoidHom, h,
    f.toIntLinearEquiv.finrank_eq]
  congr 1
  refine Nat.card_congr (f.toEquiv.subtypeEquiv ?_).symm
  intro a
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  change _ ↔ 2 • f a = 0
  rw [← map_nsmul, f.map_eq_zero_iff]
end GlobalTheory.QNorm
