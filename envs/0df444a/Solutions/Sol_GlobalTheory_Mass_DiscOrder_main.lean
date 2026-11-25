-- Prove2me | solution 1 for GlobalTheory.Mass.DiscOrder.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:08:05.52958+00:00
-- url     : https://prove2.me/submissions/74cdaa33-0090-45f7-9757-c08473a6ec14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_mul
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_eq_one
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_addData
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_lemmaS
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_gmap_locS_comm
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
namespace GlobalTheory.Mass.DiscOrder
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hn M hM
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hMd := (hint M).1 hM.2
  have h0 : ∀ N, IsIntLat h N → discN h N ≠ 0 := fun N hN => idxN_ne_zero hN.1 (dl N hN.1).1.fg
  refine ⟨h0 M hM, ?_, fun M' hM' hle => ⟨idxN_ne_zero hM.1 hM'.1.fg, ?_⟩, fun N hN => ?_,
    fun P hP hd => ?_, fun M' hM' hle P hP hu => ?_⟩
  · rw [huni, discN, idxN_eq_one]
    exact ⟨fun e => ⟨hM.2, e⟩, fun e => e.2⟩
  · have hMd' := (hint M').1 hM'.2
    rw [discN, discN, ← idxN_mul (hle.trans hMd') (an _ _ hle), ← idxN_mul hle hMd',
      idxN_dual h hs hn hM.1 _ M' hM'.1 hle rfl]
    ring
  · have hNi : IsIntLat h N := ⟨hN.1,
      (((genusBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2 M N hM.1.fg hN.1.fg hN.2).2).1 hM.2⟩
    refine ⟨hNi, genusCovol_lemmaS _ M (dual h M) N (dual h N) hMd ((hint N).1 hNi.2) rfl (h0 M hM)
      (h0 N hNi) fun P hP => ?_⟩
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg M
    have b1 := (ld (gmap g M) (a5.2 hM.1).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    refine ⟨_, g.injective, genusCovol_addData g _ _ (key _ _ hgL), genusCovol_addData g _ _ (key _ _ ?_)⟩
    rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h M)).2.1 P]
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1]
    refine le_antisymm ((locBasic_locS_mono _ fun x hx => ?_).trans (locBasic_locS_idem _ M).le)
      (locBasic_locS_mono _ hMd)
    refine ⟨(discN h M : 𝓞 K), Submonoid.subset_closure ⟨hd, fun t ht => ?_⟩, ?_⟩
    · have : t = (discN h M : 𝓞 K) := genusCovol_hinj (by rw [ht]; simp)
      rwa [this]
    · rw [Nat.cast_smul_eq_nsmul]
      have := AddSubgroup.nsmul_index_mem (H := M.toAddSubgroup.addSubgroupOf (dual h M).toAddSubgroup) ⟨x, hx⟩
      exact this
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1] at hu
    refine le_antisymm (locBasic_locS_mono _ hle) ?_
    rw [← hu]
    exact locBasic_locS_mono _ (((hint M').1 hM'.2).trans (an _ _ hle))
end GlobalTheory.Mass.DiscOrder
