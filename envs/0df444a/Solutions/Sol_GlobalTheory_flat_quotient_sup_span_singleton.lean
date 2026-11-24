-- Prove2me | solution 1 for GlobalTheory.flat_quotient_sup_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:52.503104+00:00
-- url     : https://prove2.me/submissions/1affe0b0-3176-4d43-85af-0a1145c2b3f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegular
import Theorems.Thm_GlobalTheory_mkQ_mem_smul_top_iff_mem_sup
import Theorems.Thm_GlobalTheory_flat_coker_of_injective_mod_maximalIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (V A : Type) [CommRing V] [IsNoetherianRing V]
    [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A]
    [IsLocalHom (algebraMap V A)] (J : Ideal A) [Module.Flat V (A ⧸ J)] (r : A)
    (hr : ∀ a : A, r * a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A) →
      a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A)) :
    Module.Flat V (A ⧸ (J ⊔ Ideal.span {r})) := by
  let u : (A ⧸ J) →ₗ[A] (A ⧸ J) := LinearMap.lsmul A (A ⧸ J) r
  have h := flat_coker_of_injective_mod_maximalIdeal V A (A ⧸ J) (A ⧸ J) u (by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J x
    rw [mkQ_mem_smul_top_iff_mem_sup]
    apply hr
    rw [← mkQ_mem_smul_top_iff_mem_sup]
    exact hx)
  have hu : LinearMap.range u = Submodule.map (Submodule.mkQ J) (Ideal.span {r}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J y
      exact ⟨r * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hb
      exact ⟨Submodule.mkQ J a, rfl⟩
  let e : ((A ⧸ J) ⧸ LinearMap.range u) ≃ₗ[A] (A ⧸ (J ⊔ Ideal.span {r})) :=
    (Submodule.quotEquivOfEq _ _ hu).trans
      (Submodule.quotientQuotientEquivQuotientSup J (Ideal.span {r}))
  exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm
end GlobalTheory
