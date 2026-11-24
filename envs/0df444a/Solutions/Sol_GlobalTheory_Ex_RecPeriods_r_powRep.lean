-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.r_powRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:08:03.009937+00:00
-- url     : https://prove2.me/submissions/34ad5d2b-7219-470f-b9fd-c8b8beb9dadb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_r_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution {m : ℕ} (hm : m ≠ 0) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h : μ.r (m ^ 2) p p')
    (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) : μ.r m (powRep N m p hp) (powRep N' m p' hp') := by
  have key : ∀ K, K = m * m → ∀ (a : N.QT m) (a' : N'.QT m) (q : N.QT K) (q' : N'.QT K), q.1.1 = a.1.1 ^ m →
      q.1.2 = a.1.2 → q'.1.1 = a'.1.1 ^ m → q'.1.2 = a'.1.2 → μ.r K q q' → μ.r m a a' := by
    rintro K rfl a a' q q' h₁ h₂ h₃ h₄ h
    exact (μ.incl m m a a' q q' hm h₁ h₂ h₃ h₄).2 h
  refine key _ (sq m) _ _ _ _ ?_ rfl ?_ rfl (r_pow μ h m hm)
  · change p.1.1 ^ m = 1 ^ m
    rw [hp]
  · change p'.1.1 ^ m = 1 ^ m
    rw [hp']
end GlobalTheory.Ex.RecPeriods
