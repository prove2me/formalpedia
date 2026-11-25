-- Prove2me | solution 1 for GlobalTheory.NL.Model.mem_latSpan_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:02.22007+00:00
-- url     : https://prove2.me/submissions/aed75c39-c8f6-4882-9dcc-02a214f63737

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_conv_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.NL.Model
theorem _root_.solution (a : ℤ) (f : ℤ → L) :
    f ∈ latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L)) ↔ ∀ k < a, f k = 0 := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨e, x, rfl⟩ := hf
      intro k hk
      rw [conv_single, if_neg (by omega)]
    | zero => exact fun _ _ => rfl
    | add f g _ _ hf hg => intro k hk; simp [hf k hk, hg k hk]
    | smul c f _ hf => intro k hk; simp [hf k hk]
  · intro hf
    refine Submodule.subset_span ⟨PowerSeries.mk fun j => f (a + j), (), ?_⟩
    funext k
    rw [conv_single]
    split_ifs with h
    · have : a + ((k - a).toNat : ℤ) = k := by omega
      rw [PowerSeries.coeff_mk, this, smul_eq_mul, mul_one]
    · exact hf k (by omega)
end GlobalTheory.NL.Model
