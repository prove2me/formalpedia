-- Prove2me | solution 1 for GlobalTheory.QNorm.sqSub_le_normSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:50.253228+00:00
-- url     : https://prove2.me/submissions/81bda314-ec56-4ec1-b565-f3d91967db15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    sqSub φ ≤ normSub φ δ := by
  rintro x ⟨r, hr⟩
  exact ⟨r, 0, by rw [hr]; ring⟩
end GlobalTheory.QNorm
