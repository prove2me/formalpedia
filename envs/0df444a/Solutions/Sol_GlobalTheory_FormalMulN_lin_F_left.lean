-- Prove2me | solution 1 for GlobalTheory.FormalMulN.lin_F_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:21:06.321804+00:00
-- url     : https://prove2.me/submissions/9db79c6d-d934-4486-b7d5-993048f6a2b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_lin_ev_two
import Theorems.Thm_GlobalTheory_FormalMulN_lin_F_right
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one


section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)
private lemma coeff_single_pt_eq_ite' (j j' : Fin n) (l l' : Fin d) :
    coeff (Finsupp.single (j', l') 1) (pt R d j l) = if j = j' ∧ l = l' then 1 else 0 := by
  show coeff _ (X (j, l)) = _
  rw [coeff_X]
  by_cases h : j = j' ∧ l = l'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    have h2 := Finsupp.single_left_injective one_ne_zero h'
    simp only [Prod.mk.injEq] at h2
    exact h ⟨h2.1.symm, h2.2.symm⟩
end GlobalTheory.FormalMulN
end

set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)
namespace GlobalTheory.FormalMulN
theorem _root_.solution (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if i = l then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [lin_ev_two (const_pt 1) (const_pt 0)] at h
  rw [← h]
  simp [coeff_single_pt_eq_ite', lin_F_right G]
end GlobalTheory.FormalMulN
