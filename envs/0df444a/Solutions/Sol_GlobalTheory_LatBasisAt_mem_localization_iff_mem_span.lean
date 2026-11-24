-- Prove2me | solution 1 for GlobalTheory.LatBasisAt.mem_localization_iff_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:21.347196+00:00
-- url     : https://prove2.me/submissions/bcb7cb58-1f0f-438c-bb6e-59573bc208be

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
import Theorems.Thm_GlobalTheory_LatBasisAt_mem_locRing
import Theorems.Thm_GlobalTheory_LatBasisAt_algebraMap_ne_zero
import Theorems.Thm_GlobalTheory_LatBasisAt_mem_localization_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.LatBasisAt
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.LatBasisAt
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ x ∈ Submodule.span (locRing w) (M : Set (Fin d → K)) := by
  constructor
  · intro h
    obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w M x).mp h
    have hs0 := algebraMap_ne_zero w hs
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ locRing w := (mem_locRing w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : locRing w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_localization_iff w M y).mpr ⟨1, h1, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_localization_iff w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp a.2
      refine (mem_localization_iff w M _).mpr ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy
end GlobalTheory.LatBasisAt
