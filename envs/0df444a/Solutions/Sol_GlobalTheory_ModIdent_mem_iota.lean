-- Prove2me | solution 1 for GlobalTheory.ModIdent.mem_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:25.783447+00:00
-- url     : https://prove2.me/submissions/68ad0e67-d9cd-4416-bc18-6ecc4f4f501b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsHermIsometryGraphModScalarFlagPairIota
import Theorems.Thm_GlobalTheory_ModIdent_mem_smulLat
import Theorems.Thm_GlobalTheory_ModIdent_gsmul_mem
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
open GlobalTheory GlobalTheory.ModIdent
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K]
namespace GlobalTheory.ModIdent
theorem _root_.solution (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (g : ℕ) (y' y : V) :
    (y', y) ∈ iotaGraph F F' Λ (g : 𝓞 K) ↔ y' ∈ flagPairDefinitePartLattice F' F Λ ∧ y ∈ flagPairDefinitePartLattice F F' Λ ∧
      ∃ l' ∈ Λ, ∃ m ∈ Λ, y' - l' ∈ F'.X ∧ y - (l' + (g : K) • m) ∈ F.X := by
  unfold iotaGraph
  rw [Submodule.mem_inf, Submodule.mem_prod, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h
    obtain ⟨⟨l', l⟩, ⟨⟨hl', hl⟩, hd⟩, ⟨x', x⟩, ⟨hx', hx⟩, he⟩ := Submodule.mem_sup.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hd' : l - l' ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X) := hd
    obtain ⟨u, hu, v, ⟨-, hv⟩, huv⟩ := Submodule.mem_sup.1 hd'
    obtain ⟨m, hm, rfl⟩ := (mem_smulLat g Λ u).1 hu
    refine ⟨l', hl', m, hm, by simpa using hx', ?_⟩
    have : l + x - (l' + (g : K) • m) = v + x := by
      rw [eq_sub_iff_add_eq] at huv
      rw [← huv]; abel
    rw [this]
    exact F.X.add_mem hv hx
  · rintro ⟨l', hl', m, hm, h', h⟩
    refine Submodule.mem_sup.2 ⟨(l', l' + (g : K) • m), ⟨⟨hl', Λ.add_mem hl' (gsmul_mem g hm)⟩, ?_⟩,
      (y' - l', y - (l' + (g : K) • m)), ⟨h', h⟩, by simp⟩
    show l' + (g : K) • m - l' ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)
    exact Submodule.mem_sup_left ((mem_smulLat g Λ _).2 ⟨m, hm, by abel⟩)
end GlobalTheory.ModIdent
