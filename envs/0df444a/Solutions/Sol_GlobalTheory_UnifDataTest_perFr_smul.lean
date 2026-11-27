-- Prove2me | solution 1 for GlobalTheory.UnifDataTest.perFr_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:54.4128+00:00
-- url     : https://prove2.me/submissions/c6f68a45-b130-4415-8761-ca46f9404e17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RelabBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnifDataTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
namespace GlobalTheory.UnifDataTest
theorem _root_.solution (X : Data E r) (x : Frame X.Ψ r) (b : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (b • v) τ i = τ b * perFr X x v τ i := by
  have e : ∀ ρ : E →+* ℂ, Data.emb ρ (b • v) = ρ b • Data.emb ρ v := fun ρ => by
    funext a; simp [Data.emb]
  unfold perFr
  split_ifs with h hi h' hj
  · rw [e, Matrix.mulVec_smul]; rfl
  · simp
  · rw [e]
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, conjEmb, RingHom.comp_apply,
      Complex.conj_conj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp
  · simp
end GlobalTheory.UnifDataTest
