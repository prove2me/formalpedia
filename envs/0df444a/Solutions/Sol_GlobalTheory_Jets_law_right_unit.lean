-- Prove2me | solution 1 for GlobalTheory.Jets.law_right_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:50.455634+00:00
-- url     : https://prove2.me/submissions/dca941de-1273-487c-92a0-9467995eff4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Theorems.Thm_GlobalTheory_Jets_hasSubst_pt_zero

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets
namespace GlobalTheory.Jets
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS R 1 d) := by
  have hb : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d)
  have ha : HasSubst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j <;> simp [pt])
  rw [← G.comm i, ← G.unit i]
  unfold ev
  rw [subst_comp_subst_apply ha hb]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j
  · exact subst_X hb ((1 : Fin 2), l)
  · exact subst_X hb ((0 : Fin 2), l)
end GlobalTheory.Jets
