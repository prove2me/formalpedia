-- Prove2me | solution 1 for GlobalTheory.MatchTerm.exists_torus_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:43.939259+00:00
-- url     : https://prove2.me/submissions/ad2f1605-09f2-469e-83dd-58bea4130ff2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_qeq_right
import Theorems.Thm_GlobalTheory_MatchTerm_eq_of_qeq
import Theorems.Thm_GlobalTheory_MatchTerm_thetaMatching_exists_right_torus_torsion
import Theorems.Thm_GlobalTheory_MatchTerm_thetaMatching_exists_left_torus_torsion
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
namespace GlobalTheory.MatchTerm
theorem _root_.solution (hn : n ≠ 0) (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) :
    ∃ E : {t : Multiplicative N.X →* Cˣ // t ^ k = 1} → {t : Multiplicative N'.X →* Cˣ // t ^ k = 1},
      Function.Bijective E ∧ ∀ t, μ.r k (N.qTor t.1 t.2) (N'.qTor (E t).1 (E t).2) := by
  have hk0 : k ≠ 0 := by obtain ⟨j, rfl⟩ := hk; exact pow_ne_zero _ hn
  choose f hf h using thetaMatching_exists_right_torus_torsion μ hA hk
  refine ⟨fun t => ⟨f t.1 t.2, hf t.1 t.2⟩, ⟨fun s t e => ?_, fun t' => ?_⟩, fun t => h t.1 t.2⟩
  · have e' : N'.qTor _ (hf s.1 s.2) = N'.qTor _ (hf t.1 t.2) :=
      congrArg (fun u : {t : Multiplicative N'.X →* Cˣ // t ^ k = 1} => N'.qTor u.1 u.2) e
    have h1 := h s.1 s.2
    rw [e'] at h1
    have := eq_of_qeq hk0 (μ.inj k _ _ _ h1 (h t.1 t.2)) rfl
    exact Subtype.ext (N.tor_injective (congrArg (fun q : N.QT k => q.1.2) this))
  · obtain ⟨t, ht, e⟩ := thetaMatching_exists_left_torus_torsion μ hA hk t'.1 t'.2
    refine ⟨⟨t, ht⟩, Subtype.ext (N'.tor_injective ?_)⟩
    exact congrArg (fun q : N'.QT k => q.1.2) (eq_of_qeq hk0 (qeq_right μ (h t ht) e) rfl)
end GlobalTheory.MatchTerm
