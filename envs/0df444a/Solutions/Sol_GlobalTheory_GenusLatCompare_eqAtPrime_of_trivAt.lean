-- Prove2me | solution 1 for GlobalTheory.GenusLatCompare.eqAtPrime_of_trivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:22:54.487363+00:00
-- url     : https://prove2.me/submissions/bc65043e-2109-4520-baeb-e2718a962800

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Theorems.Thm_GlobalTheory_GenusLatCompare_span_smul_le_iff

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
open GlobalTheory GlobalTheory.GenusLatCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace GlobalTheory.GenusLatCompare
theorem _root_.solution (Λ : GenLat E n) {s : ℕ} (h : Λ.TrivAt s) (p : ℕ) (hp : p.Prime) (hs : p ∣ s) :
    EqAtPrime p Λ.La (stdMod E n) := by
  obtain ⟨k, hk, h1, h2⟩ := h
  have hpk : ¬ p ∣ k := fun hd => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hk hd hs)
  rw [span_smul_le_iff] at h1 h2
  exact ⟨fun x hx => ⟨k, hpk, h1 x hx⟩, fun x hx => ⟨k, hpk, h2 x hx⟩⟩
end GlobalTheory.GenusLatCompare
