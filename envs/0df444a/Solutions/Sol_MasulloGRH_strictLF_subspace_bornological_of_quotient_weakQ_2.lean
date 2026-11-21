-- Prove2me | solution 2 for MasulloGRH.strictLF_subspace_bornological_of_quotient_weakQ
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:16:21.979958+00:00
-- url     : https://prove2.me/submissions/b8e7530b-6d54-48ff-a889-580e1e40fad4

import Theorems.Thm_MasulloGRH_strictLF_stagewise_seminorm_continuous_of_quotient_localization
import Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_weakQ
import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_localization
import Theorems.Thm_MasulloGRH_strictLF_closed_subspace_bornological_of_limit_subspace
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open MasulloGRH Set

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hwQ : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V) :
    IsBornological V := by
  obtain ⟨hE,_⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop
  have hM := strictLF_quotient_condM_of_weakQ E X hmono hexh hX htop V hV hwQ
  have hL := strictLF_quotient_regular_of_condM_localization E X hmono hexh hX htop V hV hM
  apply strictLF_closed_subspace_bornological_of_limit_subspace E X hmono hexh
    (fun n => (hX n).1) htop V hV
  obtain ⟨ι,hι,p,hp⟩ := hE.1
  have hadd := hp.topologicalAddGroup
  have hsm := hp.continuousSMul
  apply le_antisymm
  · apply le_sInf
    rintro t ⟨⟨κ,hκ,f,hf⟩,hstage⟩
    apply continuous_id_iff_le.mp
    change @Continuous V V instTopologicalSpaceSubtype t (LinearMap.id (R:=ℂ) (M:=V))
    apply (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ V V κ _ _ _ _ _ _
      (RingHom.id ℂ) _ f instTopologicalSpaceSubtype _ t hf LinearMap.id).mpr
    intro i
    apply strictLF_stagewise_seminorm_continuous_of_quotient_localization E
      hE X hmono hexh htop V hL
    intro n
    let : TopologicalSpace V := t
    exact (hf.continuous_seminorm i).comp (hstage n)
  · apply sInf_le
    refine ⟨⟨ι,hι,_,V.subtype.withSeminorms_induced hp⟩,?_⟩
    intro n
    exact continuous_subtype_val.subtype_mk _
