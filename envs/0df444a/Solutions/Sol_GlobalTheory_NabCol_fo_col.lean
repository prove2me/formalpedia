-- Prove2me | solution 1 for GlobalTheory.NabCol.fo_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:14.938809+00:00
-- url     : https://prove2.me/submissions/c95fe76e-fadc-4fb6-8f60-b1db7e6ebecf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_fo_add
import Theorems.Thm_GlobalTheory_NabCol_fo_of_zero
import Theorems.Thm_GlobalTheory_NabCol_fo_single
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
theorem _root_.solution (F : Fin d → PS k 2 d) (hF : ∀ u v, Function.Commute (Dof F u) (Dof F v)) {Λ Ix : Type} [Fintype Λ]
    [Fintype Ix] (e : Λ × Fin n → Ix) (cp : Ix → Fin n) (u : Λ → Fin d → k) (u' : Ix → Fin d → k)
    (hcp : ∀ p, cp (e p) = p.2) (hu : ∀ p, u' (e p) = u p.1) (b : Fin n) (mo : Λ × Fin n →₀ ℕ) (x : PS k 1 d) :
    fo (fun l => colD F (cp l) (u' l) b) Finset.univ.toList (Finsupp.mapDomain e mo) x =
      DmonOf F u (colM mo b) x := by
  show _ = fo (fun l => Dof F (u l)) Finset.univ.toList (colM mo b) x
  induction mo using Finsupp.induction_linear generalizing x with
  | zero => rw [fo_of_zero _ _ _ (by simp), fo_of_zero _ _ _ (by simp [colM])]
  | add m m' ih ih' =>
    have hc : colM (m + m') b = colM m b + colM m' b := by
      ext l; simp [colM]
    rw [Finsupp.mapDomain_add, hc, fo_add, fo_add _ (fun a a' => hF _ _), ih', ih]
    intro a a'
    unfold colD
    split_ifs
    · exact hF _ _
    · exact Function.Commute.id_right
    · exact Function.Commute.id_left
    · exact Function.Commute.id_left
  | single p r =>
    obtain ⟨l, c⟩ := p
    rw [Finsupp.mapDomain_single, fo_single _ _ (Finset.nodup_toList _) _ (by simp), hcp, hu]
    by_cases hcb : c = b
    · subst hcb
      have hc : colM (Finsupp.single (l, c) r) c = Finsupp.single l r := by
        classical
        ext l'; simp [colM, Finsupp.single_apply]
      rw [hc, fo_single _ _ (Finset.nodup_toList _) _ (by simp)]
      simp [colD]
    · rw [fo_of_zero _ _ _ (fun a _ => by simp [colM, Finsupp.single_apply, hcb])]
      simp [colD, hcb]
end GlobalTheory.NabCol
