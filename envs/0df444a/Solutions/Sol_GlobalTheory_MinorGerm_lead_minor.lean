-- Prove2me | solution 1 for GlobalTheory.MinorGerm.lead_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:56.429158+00:00
-- url     : https://prove2.me/submissions/8312d781-7cd9-4262-9934-0b86b938f122

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_lead_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
theorem _root_.solution (j : Fin N × Fin N' → σ) (hj : ∀ b c, p (j (b, c)) ↔ b.val = c.val) {k : ℕ}
    (hk : k ≤ min N N') :
    Lead p (∑ ρ ∈ Finset.range k, dgOne j ρ 1) (MvPolynomial.rename j (minorK C N N' k)) := by
  classical
  have h1 : k ≤ N := le_trans hk (min_le_left _ _)
  have h2 : k ≤ N' := le_trans hk (min_le_right _ _)
  have hw : ∀ b c : Fin k, p (j (Fin.castLE h1 b, Fin.castLE h2 c)) ↔ b = c := by
    intro b c
    rw [hj, Fin.val_castLE, Fin.val_castLE, Fin.val_inj]
  have hL := lead_det (C := C) (p := p) (fun b c : Fin k => j (Fin.castLE h1 b, Fin.castLE h2 c)) hw
  have hpoly : MvPolynomial.rename j (minorK C N N' k) = (Matrix.of fun b c : Fin k =>
      (MvPolynomial.X (j (Fin.castLE h1 b, Fin.castLE h2 c)) : MvPolynomial σ C)).det := by
    unfold minorK
    rw [dif_pos ⟨h1, h2⟩, AlgHom.map_det]
    congr 1
    ext b c
    simp [MvPolynomial.rename_X]
  have hexp : ∑ ρ ∈ Finset.range k, dgOne j ρ 1 =
      ∑ b : Fin k, Finsupp.single (j (Fin.castLE h1 b, Fin.castLE h2 b)) 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun ρ => dgOne j ρ 1) k]
    apply Finset.sum_congr rfl
    intro b _
    unfold dgOne
    rw [dif_pos ⟨lt_of_lt_of_le b.isLt h1, lt_of_lt_of_le b.isLt h2⟩]
    rfl
  rw [hpoly, hexp]
  exact hL
end GlobalTheory.MinorGerm
