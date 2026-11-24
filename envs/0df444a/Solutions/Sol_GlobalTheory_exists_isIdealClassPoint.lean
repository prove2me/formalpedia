-- Prove2me | solution 1 for GlobalTheory.exists_isIdealClassPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:04.8348+00:00
-- url     : https://prove2.me/submissions/59267d39-f199-4a29-96df-06b4bfcd5536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_exists_classRep_periodPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
    (c : ClassGroup (𝓞 K)) : ∃ τ, IsIdealClassPoint σ c τ := by
  obtain ⟨𝔞, L, h1, hL⟩ := exists_classRep_periodPair h2 hD σ c
  obtain ⟨ω, τ, -, h⟩ := exists_lattice_eq_mul_tau L
  exact ⟨τ, 𝔞, ω, h1, fun z => by rw [← hL, SetLike.mem_coe, h]⟩
end GlobalTheory
