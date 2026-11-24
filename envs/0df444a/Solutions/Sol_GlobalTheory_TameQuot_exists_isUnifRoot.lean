-- Prove2me | solution 1 for GlobalTheory.TameQuot.exists_isUnifRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:47.547903+00:00
-- url     : https://prove2.me/submissions/843177d0-ab84-419e-a5ac-f94818fe17cf

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.TameQuot
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace GlobalTheory.TameQuot
theorem _root_.solution [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    ∃ x : Ω, IsUnifRoot v N x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨ϖ, h1, h2⟩ :=
    Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (ϖ : F)) hN
  exact ⟨x, ϖ, by simpa using h1, h2, hx⟩
end GlobalTheory.TameQuot
