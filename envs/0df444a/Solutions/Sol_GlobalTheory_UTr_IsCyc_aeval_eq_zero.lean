-- Prove2me | solution 1 for GlobalTheory.UTr.IsCyc.aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:03.458889+00:00
-- url     : https://prove2.me/submissions/fa8723eb-d336-4937-9351-ce12c4814056

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Theorems.Thm_GlobalTheory_UTr_aeval_mulMat_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.UTr
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : Csr s)
variable {n : Type} [Fintype n] [DecidableEq n]
variable {J : Matrix n n B}
variable {P}
variable {x x' : Alg P}
namespace GlobalTheory.UTr
namespace IsCyc
theorem _root_.solution {g : Matrix n n B} (h : IsCyc P g) : aeval g P.1 = 0 := by
  obtain ⟨i, rfl⟩ := h; exact aeval_mulMat_root i
end IsCyc
end GlobalTheory.UTr
