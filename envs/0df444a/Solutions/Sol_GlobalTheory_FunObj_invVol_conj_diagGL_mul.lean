-- Prove2me | solution 1 for GlobalTheory.FunObj.invVol_conj_diagGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:31.840466+00:00
-- url     : https://prove2.me/submissions/f4581462-77ad-4292-b77b-4dbc3c262cbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Theorems.Thm_GlobalTheory_FunObj_idxRatio_map
import Theorems.Thm_GlobalTheory_FunObj_idxRatio_cocycle
import Theorems.Thm_P2M_GlobalTheory_FunObj_diagGL_mul__bb3860aff896
import Theorems.Thm_GlobalTheory_FunObj_map_conj_diagGL_symN
import Theorems.Thm_GlobalTheory_FunObj_invVol_eq_idxRatio
import Theorems.Thm_GlobalTheory_FunObj_isOpen_map_conj_KO
import Theorems.Thm_GlobalTheory_FunObj_isCompact_map_conj_KO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.FunObj
theorem _root_.solution (d e : n ⊕ Fin c → kˣ) :
    invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) =
      invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) *
        invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  have hmapN : ∀ (d : n ⊕ Fin c → kˣ) (K' : Subgroup (GL (n ⊕ Fin c) k)),
      (symN k n c ⊓ K').map (MulAut.conj (diagGL d)).toMonoidHom =
        symN k n c ⊓ K'.map (MulAut.conj (diagGL d)).toMonoidHom := by
    intro d K'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (diagGL d)).injective, map_conj_diagGL_symN]
  have hcomp : (KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom =
      ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom).map
        (MulAut.conj (diagGL d)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, diagGL_mul']
    group
  rw [invVol_eq_idxRatio, invVol_eq_idxRatio, invVol_eq_idxRatio, hcomp,
    ← idxRatio_cocycle (symN k n c) isOpen_KO isCompact_KO (isOpen_map_conj_KO (diagGL d))
      (isCompact_map_conj_KO (diagGL d)) (hcomp ▸ isOpen_map_conj_KO (diagGL (d * e)))
      (hcomp ▸ isCompact_map_conj_KO (diagGL (d * e)))]
  congr 1
  rw [← hmapN d (KO k _), ← hmapN d ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom),
    idxRatio_map (MulAut.conj (diagGL d)).injective]
end GlobalTheory.FunObj
