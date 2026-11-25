-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.exists_eich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:04:21.707057+00:00
-- url     : https://prove2.me/submissions/07c35a05-029a-4b19-8001-a6076314fdc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_le
import Theorems.Thm_P2M_GlobalTheory_DegCnt_PosIso_Ia_le__b4a7964e0214
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_X
import Theorems.Thm_P2M_GlobalTheory_DegCnt_PosIso_Ia_X__933463d23d40
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_eich_apply
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_eich_inN
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eichlerMapIsometry
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_sup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (x v : V) (c : K) (hx : x ∈ Ia N r) (hxv : H.B x v = 0)
    (hc : c + star c = -H.B v v)
    (hlev : ∀ a : Fin r, N.j ≤ a.val → H.B (N.F.e a.castSucc) v • x ∈ Ia N a.val)
    (h1 : ∀ a : Fin r, a.val < N.j → H.B (N.F.e a.castSucc) v = 0)
    (h2 : ∀ a : Fin r, a.val < N.j → H.B (N.F'.e a.castSucc) v = 0)
    (hW : v ∈ V0 N.F N.F' ⊔ N.Ist) :
    ∃ s ∈ Gs N, ∀ y, H.B y x = 0 → s y = y + H.B y v • x := by
  obtain ⟨-, e2, e3⟩ := eichlerMapIsometry K V H x v c (X_iso N.F (Ia_X N hx) (Ia_X N hx)) hxv hc
  let s : V ≃ₗ[K] V := LinearEquiv.ofLinear (eich H x v c) (eich H x (-v) (star c))
    (LinearMap.ext e3) (LinearMap.ext e2)
  have hs : ∀ y, H.B y x = 0 → s y = y + H.B y v • x := by
    intro y hy
    show eich H x v c y = _
    simp [eich_apply, hy]
  refine ⟨s, ⟨⟨Subgroup.subset_closure ⟨?_, ?_⟩, ?_⟩, ?_⟩, hs⟩
  · refine eich_inN N.F x v c (Ia_X N hx) hxv hc fun a => ?_
    by_cases h : a.val < N.j
    · simp [h1 a h]
    · exact Ia_le N _ (hlev a (not_lt.1 h))
  · refine eich_inN N.F' x v c (Ia_X' N hx) hxv hc fun a => ?_
    by_cases h : a.val < N.j
    · simp [h2 a h]
    · rw [N.same _ (not_lt.1 h), map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ _ (Ia_le' N _ (hlev a (not_lt.1 h)))
  · refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    have hy' := (mem_perp_iff H _ y).1 hy
    show s y = y
    rw [hs y (hy' x (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Ia_X N hx))))),
      hy' v hW]
    simp
  · refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    show s y = y
    rw [hs y (perp_sup H (fun u hu => X_iso N.F (Xa_le_X _ _ hu) (Ia_X N hx))
      (fun u hu => X_iso N.F' (Xa_le_X _ _ hu) (Ia_X' N hx)) y hy),
      perp_sup H (perp_Xa N.F h1) (perp_Xa N.F' h2) y hy]
    simp
end GlobalTheory.DegCnt.PosIso
