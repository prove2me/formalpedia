-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_sequentially_retractive_of_bounded_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:57:25.118551+00:00
-- url     : https://prove2.me/submissions/41b07c9f-adc0-4ff0-b9f5-ea41ee6b5564

import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_iff_bounded_lifting
import Theorems.Thm_MasulloGRH_nuclearFrechet_quotient_bounded_compact_closure
import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

open Set Filter Topology

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlift : LiftsBoundedSets (V.mkQ : E → E ⧸ V))
    (u : ℕ → E ⧸ V) (hu : Filter.Tendsto u Filter.atTop (nhds 0)) :
    ∃ (n : ℕ) (v : ℕ → X n ⧸ V.comap (X n).subtype),
      (∀ j, Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl (v j) = u j) ∧
      Filter.Tendsto v Filter.atTop (nhds 0) := by
  classical
  obtain ⟨⟨⟨ι, _, p, hp⟩, hT⟩, _⟩ :=
    bounded_in_strict_frechet_stages E X hmono hexh (fun n => (hX n).1) htop
  letI := hp.topologicalAddGroup
  letI := hp.continuousSMul
  letI := hT
  haveI : IsClosed (V.toAddSubgroup : Set E) := hV
  haveI : T2Space (E ⧸ V) := inferInstance
  have hreg := (strictLF_quotient_regular_iff_bounded_lifting E X hmono hexh hX htop V hV).mp hlift
  obtain ⟨n, A, hA, hcover⟩ := hreg (insert 0 (range u)) ((hu.isVonNBounded_range ℂ).insert 0)
  let W := V.comap (X n).subtype
  let f := Submodule.mapQ W V (X n).subtype le_rfl
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker (Submodule.mapQ W V (X n).subtype le_rfl) = ⊥
    rw [Submodule.ker_mapQ]
    exact W.mkQ_map_self
  have hc : Continuous f := (W.isQuotientMap_mkQL.continuous_iff).mpr
    (V.continuous_mkQ.comp continuous_subtype_val)
  have hW : IsClosed (W : Set (X n)) := hV.preimage continuous_subtype_val
  have hK := nuclearFrechet_quotient_bounded_compact_closure (X n) (hX n).1 (hX n).2 W hW A hA
  letI : CompactSpace (closure A) := isCompact_iff_compactSpace.mp hK
  let g : closure A → E ⧸ V := fun a => f a.val
  have hg : IsEmbedding g := ((hc.comp continuous_subtype_val).isClosedEmbedding
    (hf.comp Subtype.val_injective)).isEmbedding
  have hz : (0 : X n ⧸ W) ∈ closure A := by
    obtain ⟨a, ha, ha0⟩ := hcover (mem_insert 0 _)
    have : a = 0 := hf (ha0.trans f.map_zero.symm)
    exact this ▸ subset_closure ha
  have hpre (j : ℕ) : ∃ a : closure A, g a = u j := by
    obtain ⟨a, ha, heq⟩ := hcover (mem_insert_of_mem 0 (mem_range_self j))
    exact ⟨⟨a, subset_closure ha⟩, heq⟩
  choose v hv using hpre
  let z : closure A := ⟨0, hz⟩
  have hv0 : Tendsto v atTop (𝓝 z) := hg.tendsto_nhds_iff.mpr (by
    have hcomp : g ∘ v = u := funext hv
    rw [hcomp]
    simpa [g, z] using hu)
  exact ⟨n, fun j => (v j).val, hv, continuous_subtype_val.continuousAt.tendsto.comp hv0⟩
