-- Prove2me | solution 1 for GlobalTheory.BetaEx.frac_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:20.027799+00:00
-- url     : https://prove2.me/submissions/78270006-5ec8-4a9b-a9fe-d025fe84a5f9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_mem_detSet
import Theorems.Thm_GlobalTheory_BetaEx_mem_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
omit [NumberField E]
namespace GlobalTheory.BetaEx
theorem _root_.solution {M : Submodule (𝓞 E) (Fin n → E)} (h : Bdd M) :
    IsFractional (nonZeroDivisors (𝓞 E)) (detSpan M) := by
  obtain ⟨k, hk, h⟩ := h
  apply FractionalIdeal.isFractional_span_iff.2
  refine ⟨k ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hk), ?_⟩
  intro d hd
  obtain ⟨v, hv, rfl⟩ := (mem_detSet M d).1 hd
  choose b hb using fun i => (mem_std _).1 (h _ (hv i))
  refine ⟨(Matrix.of b).det, ?_⟩
  rw [RingHom.map_det]
  have : (algebraMap (𝓞 E) E).mapMatrix (Matrix.of b) = (k : E) • v := by
    ext i j
    exact hb i j
  rw [this, Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
end GlobalTheory.BetaEx
