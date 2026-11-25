-- Prove2me | solution 1 for GlobalTheory.DegAsm.NFUnique.exists_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:27.028003+00:00
-- url     : https://prove2.me/submissions/3dd40fcc-29c6-4ee6-af2e-15b287c7986e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
import Theorems.Thm_GlobalTheory_DegAsm_NFUnique_Cmp_symm
import Theorems.Thm_GlobalTheory_DegAsm_NFUnique_cmp_span_left
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_comp
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.NFUnique
theorem _root_.solution (S : Set (V × V)) (h : ∀ p ∈ S, ∀ q ∈ S, Cmp H p q)
    (h1 : (Submodule.span K S).map (LinearMap.fst K V V) = ⊤)
    (h2 : (Submodule.span K S).map (LinearMap.snd K V V) = ⊤) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ ∀ p ∈ S, s p.1 = p.2 := by
  have hG : ∀ p ∈ Submodule.span K S, ∀ q ∈ Submodule.span K S, Cmp H p q := fun p hp q hq =>
    cmp_span_left (fun p hp => (cmp_span_left (fun q hq => h q hq p hp) q hq).symm) p hp
  set G := Submodule.span K S with hGdef
  have s1 : ∀ v : V, ∃ p : G, p.1.1 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h1.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have s2 : ∀ v : V, ∃ p : G, p.1.2 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h2.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have b1 : Function.Bijective ((LinearMap.fst K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s1⟩
    have e1 : p.1.1 = 0 := hp
    refine Subtype.ext (Prod.ext e1 (H.nondeg _ fun y => ?_))
    obtain ⟨q, rfl⟩ := s2 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this.symm
  have b2 : Function.Bijective ((LinearMap.snd K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s2⟩
    have e1 : p.1.2 = 0 := hp
    refine Subtype.ext (Prod.ext (H.nondeg _ fun y => ?_) e1)
    obtain ⟨q, rfl⟩ := s1 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this
  have key : ∀ p : G, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) p.1.1 = p.1.2 := by
    intro p
    have : (LinearEquiv.ofBijective _ b1).symm p.1.1 = p := (LinearEquiv.symm_apply_eq _).2 rfl
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨_, fun x y => ?_, fun p hp => key ⟨p, Submodule.subset_span hp⟩⟩
  obtain ⟨p, rfl⟩ := s1 x
  obtain ⟨q, rfl⟩ := s1 y
  rw [key, key]
  exact Eq.symm (hG _ p.2 _ q.2)
end GlobalTheory.DegAsm.NFUnique
