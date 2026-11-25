-- Prove2me | solution 1 for GlobalTheory.DegCnt.count_index_latMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:57.520558+00:00
-- url     : https://prove2.me/submissions/b1c699d4-f74f-4e50-a4e9-f64daf49696b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesDefiniteQuotientNormalFormLe
import Theorems.Thm_GlobalTheory_DegCnt_count_index_fg
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt
namespace GlobalTheory.DegCnt
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (W I : Submodule K V)
    (La : Submodule (𝓞 K) V) (h : IsLatMod La (W ⊔ I) I) (x : ℕ) (hx : 1 ≤ x) :
    ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ ((Module.finrank K W : ℝ) + cf K)) := by
  obtain ⟨⟨N, hN, hLa⟩, hsp⟩ := h
  let q : V →ₗ[𝓞 K] (V ⧸ I) := I.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker q = rs (𝓞 K) I := by
    ext v; simp [q]
  have hM : (La.map q).FG := by
    have : (rs (𝓞 K) I).map q = ⊥ := by
      rw [← hker]; exact LinearMap.le_ker_iff_map.1 le_rfl
    rw [hLa, Submodule.map_sup, this, sup_bot_eq]
    exact hN.map q
  have hS : La.map q ≤ (W.map I.mkQ).restrictScalars (𝓞 K) := by
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ W ⊔ I := hsp ▸ Submodule.subset_span hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 this
    refine ⟨w, hw, ?_⟩
    have : I.mkQ u = 0 := by simpa using hu
    change I.mkQ w = I.mkQ (w + u)
    rw [map_add, this, add_zero]
  obtain ⟨h1, h2⟩ := count_index_fg (La.map q) hM (W.map I.mkQ) hS _ (Submodule.finrank_map_le _ _) x hx
  have hle : {Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}.encard ≤
      {N : Submodule (𝓞 K) (La.map q) | N.toAddSubgroup.index = x}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun Th => (Th.map q).comap (La.map q).subtype) ?_ ?_
    · rintro Th ⟨hI, hL, hi⟩
      have e : (Th.map q).comap q = Th := Submodule.comap_map_eq_self (hker ▸ hI)
      have e2 : idx La ((Th.map q).comap q) = idx (La.map q) (Th.map q) :=
        AddSubgroup.relIndex_comap (Th.map q).toAddSubgroup q.toAddMonoidHom La.toAddSubgroup
      rw [e, hi] at e2
      exact e2.symm
    · rintro Th ⟨hI, hL, -⟩ Th' ⟨hI', hL', -⟩ he
      have he2 : Th.map q = Th'.map q := by
        have := congrArg (Submodule.map (La.map q).subtype) he
        simp only [Submodule.map_comap_subtype] at this
        rwa [inf_eq_right.2 (Submodule.map_mono hL), inf_eq_right.2 (Submodule.map_mono hL')] at this
      rw [← Submodule.comap_map_eq_self (f := q) (p := Th) (hker ▸ hI), he2,
        Submodule.comap_map_eq_self (hker ▸ hI')]
  refine le_trans (ENat.toENNReal_le.2 hle) ?_
  rw [← h1.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h2
end GlobalTheory.DegCnt
