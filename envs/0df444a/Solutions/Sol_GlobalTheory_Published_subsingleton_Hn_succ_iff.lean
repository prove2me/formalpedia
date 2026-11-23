-- Prove2me | solution 1 for GlobalTheory.Published.subsingleton_Hn_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:29.195651+00:00
-- url     : https://prove2.me/submissions/351ca6bb-93b3-4a91-90d9-803a3ce202d6

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published
variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type*} [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M]
namespace GlobalTheory.Published
theorem _root_.solution {R : Type*} [CommRing R] [Module R M] [ContinuousConstSMul R M]
    (rho : Representation R Γ M) (n : ℕ) :
    Subsingleton (Hn rho (n + 1)) ↔
      ∀ f : (Fin (n + 1) → Γ) → M, Continuous f → dn rho (n + 1) f = 0 →
        ∃ c : (Fin n → Γ) → M, Continuous c ∧ dn rho n c = f := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h f hf hd
    exact h (x := ⟨f, hf, hd⟩) trivial
  · intro h f _
    exact h f.1 f.2.1 f.2.2
end GlobalTheory.Published
