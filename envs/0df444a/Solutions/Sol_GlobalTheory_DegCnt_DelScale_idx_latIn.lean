-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.idx_latIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:29:40.961895+00:00
-- url     : https://prove2.me/submissions/6188d30c-0d3d-40d4-a4c9-88c0c906a72f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_sup
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DelScale
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {S I C : Submodule K V} (p : V →ₗ[K] V) (hCS : C ≤ S) (hpC : ∀ x ∈ S, p x ∈ C)
  (hpI : ∀ x, x - p x ∈ I) (hI : ∀ x ∈ I, p x = 0) (hC : ∀ x ∈ C, p x = x)
omit [NumberField K] [StarRing K] [FiniteDimensional K V]
include hpC hpI
namespace GlobalTheory.DegCnt.DelScale
theorem _root_.solution {A B : Submodule (𝓞 K) V} (hA : rs (𝓞 K) I ≤ A) (hAS : A ≤ rs (𝓞 K) S)
    (hB : rs (𝓞 K) I ≤ B) : idx (latIn C A) (latIn C B) = idx A B := by
  have e : A = (A ⊓ rs (𝓞 K) C) ⊔ rs (𝓞 K) I := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hA)
    have h1 : x - p x ∈ A := hA (hpI x)
    have h2 : p x ∈ A := by simpa using A.sub_mem hx h1
    have : x = p x + (x - p x) := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨h2, hpC x (hAS hx)⟩ (hpI x)
  have e2 : idx A B = idx (A ⊓ rs (𝓞 K) C) B := by
    conv_lhs => rw [e]
    exact idx_sup hB
  rw [e2]
  have := AddSubgroup.relIndex_comap B.toAddSubgroup C.subtype.toAddMonoidHom (latIn C A).toAddSubgroup
  refine this.trans ?_
  unfold idx
  congr 1
  ext x
  simp only [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h2⟩, h1, rfl⟩
end GlobalTheory.DegCnt.DelScale
