-- Prove2me | solution 1 for GlobalTheory.SplitComp.compAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:40.860087+00:00
-- url     : https://prove2.me/submissions/c74a749a-d313-4245-8cc7-09d7694f3aa7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
import Theorems.Thm_GlobalTheory_SplitComp_exists_imag
import Theorems.Thm_GlobalTheory_SplitComp_exists_tmul_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
open GlobalTheory GlobalTheory.SplitComp
variable (L : Type) [Field L] [NumberField L] [IsCMField L]
namespace GlobalTheory.SplitComp
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L),
    s.proj z = 0 → s.proj (conjAL L z) = 0 → compAt L s.v z = 0 := by
  intro L _ _ _ s z h1 h2
  obtain ⟨θ, h0, hθ⟩ := exists_imag L
  obtain ⟨a, b, rfl⟩ := exists_tmul_add L θ h0 hθ z
  have e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj] using h1
  have e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj, conjAL, hθ, neg_tmul, sub_eq_add_neg] using h2
  have hi : s.i θ ≠ 0 := (map_ne_zero s.i).mpr h0
  have : CharZero (s.v.adicCompletion (maximalRealSubfield L)) :=
    algebraRat.charZero _
  have ha : evalAt L s.v a = 0 := by linear_combination (e1 + e2) / 2
  have hb : evalAt L s.v b = 0 := by
    rw [ha, zero_add] at e1
    exact (mul_eq_zero.mp e1).resolve_left hi
  simp [compAt, ha, hb]
end GlobalTheory.SplitComp
