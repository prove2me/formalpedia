-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_genConf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:35.964732+00:00
-- url     : https://prove2.me/submissions/8847c805-fd29-43b6-a250-d0d3784dda69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_selfDual_splitLat
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_primIn_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {g : ℕ} (hg : g ≠ 0) {a b : 𝓞 E}
    (hab : differentIdeal ℤ (𝓞 E) = Ideal.span {a, b}) :
    ((splitLat E, splitP E, splitQ σ g (a : E) (b : E)) : Tri E 8 1) ∈
      GenConf σ (splitJ E) 1 (1 + 2 * g) g
        !![(g : E) * splitC σ g (a : E) (b : E), 0; 0, -1 - (g : E)] := by
  refine ⟨selfDual_splitLat σ hσ,
    ⟨⟨⟨!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1], ?_⟩, ?_⟩,
      ⟨⟨!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 1], ?_⟩, ?_⟩, ?_⟩, primIn_split σ hσ hg hab⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitP, Matrix.mul_apply, Fin.sum_univ_eight]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairM, cT, TF, splitP, splitJ, Matrix.mul_apply, Fin.sum_univ_eight]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitQ, Matrix.mul_apply, Fin.sum_univ_eight]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairM, cT, TF, splitQ, splitC, splitJ, hσ, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairM, cT, splitP, splitQ, splitJ, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring
end GlobalTheory.SgGlob.Inhab
