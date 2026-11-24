-- Prove2me | solution 1 for GlobalTheory.GenusLatCompare.exists_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:05:58.754573+00:00
-- url     : https://prove2.me/submissions/ba14b6d6-e0cd-47e5-a6d9-c36e40aab100

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan

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
omit [NumberField E]
namespace GlobalTheory.GenusLatCompare
theorem _root_.solution {p : ℕ} (hp : p.Prime) {A B : Submodule (𝓞 E) (Fin n → E)} (hA : A.FG)
    (h : ∀ x ∈ A, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ B) : ∃ k : ℕ, ¬ p ∣ k ∧ ∀ x ∈ A, k • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! k hk using h
  refine ⟨∏ s ∈ S, k s, ?_, ?_⟩
  · rw [Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨s, hs, hd⟩
    exact (hk s (Submodule.subset_span hs)).1 hd
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [← Finset.prod_erase_mul S k hs, mul_smul]
      exact B.toAddSubmonoid.nsmul_mem (hk s (Submodule.subset_span hs)).2 _
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact B.smul_mem _ hx
end GlobalTheory.GenusLatCompare
