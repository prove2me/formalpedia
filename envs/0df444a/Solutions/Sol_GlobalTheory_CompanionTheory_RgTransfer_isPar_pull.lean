-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.isPar_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:34.002979+00:00
-- url     : https://prove2.me/submissions/3bcb5341-e747-41b5-8e9c-d31ef1251c2d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution [IsTopologicalGroup G] (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    (hP : IsPull Q P P' π c₀ c c') (h : IsPar Γ' K' P' c') : IsPar (Γ ⊓ Q) K P c := by
  have hPQ : P ≤ Q := fun g hg => ((hP.mem g).1 hg).1
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · have : (P : Set G) = Subtype.val '' (π ⁻¹' (P' : Set G')) := by
      ext g
      constructor
      · intro hg
        obtain ⟨h1, h2⟩ := (hP.mem g).1 hg
        exact ⟨⟨g, h1⟩, h2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact (hP.mem _).2 ⟨q.2, hq⟩
    rw [this]
    exact hL.par.closed.isClosedEmbedding_subtypeVal.isClosedMap _ (h.closed.preimage hL.contπ)
  · intro g
    obtain ⟨q, k, hg⟩ := exists_qk hL g
    obtain ⟨p', hp', k', hk', hq⟩ := h.iwa (π q)
    set m : K' := ⟨k', hk'⟩ with hm
    refine ⟨((q * ι k'⁻¹ : Q) : G), (hP.mem _).2 ⟨Subtype.property _, ?_⟩, ((kι hL m * k : K) : G),
      Subtype.property _, ?_⟩
    · show π (q * ι k'⁻¹) ∈ P'
      have : π (q * ι k'⁻¹) = p' := by
        simp [map_mul, map_inv, hL.sect, hq]
      rw [this]
      exact hp'
    · simp [hg, hm]
  · intro p hp q hq
    obtain ⟨hp1, hp2⟩ := (hP.mem _).1 hp
    obtain ⟨hq1, hq2⟩ := (hP.mem _).1 hq
    have h1 := hP.ch ⟨p, hp1⟩ hp2
    have h2 := hP.ch ⟨q, hq1⟩ hq2
    have h3 := hP.ch (⟨p, hp1⟩ * ⟨q, hq1⟩) (by rw [map_mul]; exact P'.mul_mem hp2 hq2)
    have h4 := c₀_mul hL ⟨p, hp1⟩ ⟨q, hq1⟩
    rw [map_mul, h4, h.ch.mul _ hp2 _ hq2] at h3
    simp only [Subgroup.coe_mul] at h3 h1 h2
    rw [h3, h1, h2]
    ring
  · intro p hp
    obtain ⟨hp1, hp2⟩ := (hP.mem _).1 hp
    have h1 := hP.ch ⟨p, hp1⟩ hp2
    simp only at h1
    rw [h1, norm_mul, hL.par.ch.norm p hp1, h.ch.norm _ hp2, one_mul]
  · intro γ hγ hγP
    obtain ⟨hp1, hp2⟩ := (hP.mem _).1 hγP
    have h1 := hP.ch ⟨γ, hp1⟩ hp2
    simp only at h1
    rw [h1, hL.par.ch.rat γ hγ.1 hp1, h.ch.rat _ (hL.πΓ ⟨γ, hp1⟩ hγ.1) hp2, one_mul]
  · rw [continuousOn_iff_continuous_restrict]
    have hin : Continuous fun p : P => (⟨p, hPQ p.2⟩ : Q) :=
      Continuous.subtype_mk continuous_subtype_val _
    have hc₀ : Continuous fun q : Q => c₀ q :=
      continuousOn_iff_continuous_restrict.1 hL.par.ch.cont
    have hc' : Continuous fun q : P' => c' q :=
      continuousOn_iff_continuous_restrict.1 h.ch.cont
    have hπ : Continuous fun p : P => (⟨π ⟨p, hPQ p.2⟩, ((hP.mem _).1 p.2).2⟩ : P') :=
      Continuous.subtype_mk (hL.contπ.comp hin) _
    refine ((hc₀.comp hin).mul (hc'.comp hπ)).congr (fun p => ?_)
    have := hP.ch ⟨p, hPQ p.2⟩ ((hP.mem _).1 p.2).2
    exact this.symm
end GlobalTheory.CompanionTheory.RgTransfer
