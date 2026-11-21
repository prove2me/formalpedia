-- Prove2me | solution 1 for MasulloGRH.strictLF_limit_subspace_of_bornological
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:49:15.949181+00:00
-- url     : https://prove2.me/submissions/80aab3ee-b0d5-46c9-84ad-58cdad4c953c

import Theorems.Thm_MasulloGRH_bounded_sets_strict_inductive_limit
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open MasulloGRH Set Bornology Topology

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hborn : IsBornological V) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}  := by
  classical
  obtain ⟨hE,hcl⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop
  obtain ⟨ι, hi, p,hp⟩ := hE.1
  have hadd := hp.topologicalAddGroup
  have hs := hp.continuousSMul
  have hpV : WithSeminorms (p.comp V.subtype) := V.subtype.withSeminorms_induced hp
  apply le_antisymm
  · apply le_sInf
    rintro t ⟨⟨κ,hκ,q,hq⟩,hstage⟩
    let : TopologicalSpace V := instTopologicalSpaceSubtype
    apply continuous_id_iff_le.mp
    change @Continuous V V _ t (LinearMap.id (R:=ℂ) (M:=V))
    apply (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ V V κ _ _ _ _ _ _
      (RingHom.id ℂ) _ q _ _ t hq LinearMap.id).mpr
    intro i
    apply hborn
    intro B hB
    have hEB := hB.image V.subtypeL
    obtain ⟨n,A,hA,heq⟩ := (bounded_sets_strict_inductive_limit E hE X hmono hexh hcl htop _).mp hEB
    let Y := V ⊓ X n
    let inc : Y →ₗ[ℂ] V := Submodule.inclusion inf_le_left
    let D := inc ⁻¹' B
    have hpY : WithSeminorms (p.comp Y.subtype) := Y.subtype.withSeminorms_induced hp
    have hD : IsVonNBounded ℂ D := by
      apply hpY.isVonNBounded_iff_seminorm_bddAbove.mpr
      intro j
      refine ((hp.isVonNBounded_iff_seminorm_bddAbove.mp hEB) j).mono ?_
      rintro _ ⟨y,hy,rfl⟩
      exact ⟨(y:E),⟨inc y,hy,rfl⟩,rfl⟩
    have hqinc : Continuous ((q i).comp inc) := by
      let : TopologicalSpace V := t
      exact (hq.continuous_seminorm i).comp (hstage n)
    have hpoly := hpY.toPolynormableSpace
    have hbdd := ((PolynormableSpace.withSeminorms ℂ Y).isVonNBounded_iff_seminorm_bddAbove.mp hD)
      ⟨(q i).comp inc,hqinc⟩
    refine hbdd.mono ?_
    rintro _ ⟨y,hy,rfl⟩
    have hyA : (y:E) ∈ Subtype.val '' A := heq ▸ ⟨y,hy,rfl⟩
    obtain ⟨z,hz,hez⟩ := hyA
    have hyX : (y:E) ∈ X n := hez ▸ z.property
    let v : Y := ⟨y, y.property, hyX⟩
    exact ⟨v,hy,rfl⟩
  · apply sInf_le
    refine ⟨⟨ι,hi,_,hpV⟩,?_⟩
    intro n
    exact continuous_subtype_val.subtype_mk _
