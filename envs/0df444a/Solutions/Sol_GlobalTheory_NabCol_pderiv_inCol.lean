-- Prove2me | solution 1 for GlobalTheory.NabCol.pderiv_inCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:45.998541+00:00
-- url     : https://prove2.me/submissions/b69d2880-4edb-4280-ab8d-4031bc9aaa82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_subst


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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory GlobalTheory.NabCol
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.NabCol
theorem _root_.solution (b c : Fin n) (j : Fin d) (f : PS k 1 d) :
    pderiv k (c, j) (inCol b f) = if b = c then inCol b (pderiv k ((0 : Fin 1), j) f) else 0 := by
  unfold inCol ev
  rw [FormalLog.pderiv_subst (a := fun p : Fin 1 × Fin d => (![pt k d b] : Fin 1 → Pt k n d) p.1 p.2)
    (fun p => gp b p.1 p.2)]
  have e : ∀ p : Fin 1 × Fin d, (![pt k d b] : Fin 1 → Pt k n d) p.1 p.2 = X (b, p.2) := by
    rintro ⟨a, i⟩
    fin_cases a
    rfl
  split_ifs with hbc
  · subst hbc
    rw [Finset.sum_eq_single ((0 : Fin 1), j)]
    · rw [e, pderiv_X_self, mul_one]
    · rintro ⟨a, i⟩ _ hne
      have hb : i ≠ j := fun h => hne (by subst h; rw [Subsingleton.elim a 0])
      rw [e, pderiv_X_of_ne (fun h => hb (congrArg Prod.snd h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun p _ => ?_
    rw [e, pderiv_X_of_ne (fun h => hbc (congrArg Prod.fst h)), mul_zero]
end GlobalTheory.NabCol
