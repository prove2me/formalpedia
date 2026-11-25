-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:36:46.079389+00:00
-- url     : https://prove2.me/submissions/09d11750-eec2-40bc-b051-9eb27f76fa19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameMove
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegAsm.FrameMove
theorem _root_.solution (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  classical
  let q : V →ₗ[𝓞 K] V ⧸ W := W.mkQ.restrictScalars (𝓞 K)
  let Lb : Submodule (𝓞 K) (V ⧸ W) := L.map q
  have hfin : Module.Finite (𝓞 K) Lb := Module.Finite.iff_fg.2 (hfg.map q)
  have hcancel : ∀ (d : 𝓞 K) (x : V ⧸ W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left (by simpa using hd)
  have hflat : Module.Flat (𝓞 K) Lb := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : 𝓞 K) • (x : V ⧸ W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  have hfp : Module.FinitePresentation (𝓞 K) Lb := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 K) Lb := Module.Flat.projective_of_finitePresentation
  let qL : L →ₗ[𝓞 K] Lb := q.submoduleMap L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qL LinearMap.id (LinearMap.submoduleMap_surjective q L)
  have hs' : ∀ y : Lb, q (s y : V) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let p0 : L →ₗ[𝓞 K] V := L.subtype - L.subtype ∘ₗ s ∘ₗ qL
  have hp0 : ∀ x : L, p0 x = (x : V) - s (qL x) := fun x => rfl
  have hden : ∀ v : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
    intro v
    have hv : v ∈ Submodule.span K (L : Set V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  have hunit : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) V) x) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
    refine ⟨hunit, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let P0 : V →ₗ[𝓞 K] V := IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype p0 hunit
  have hP0 : ∀ x : L, P0 (x : V) = p0 x := fun x => IsLocalizedModule.lift_apply _ L.subtype p0 hunit x
  let P : V →ₗ[K] V := P0.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
  have hP : ∀ v, P v = P0 v := fun v => rfl
  have hW : ∀ x : L, p0 x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    change q (p0 x) = 0
    rw [hp0, map_sub, hs']
    exact sub_self _
  refine ⟨P, fun v => ?_, fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨d, hd, hv⟩ := hden v
    rw [← Submodule.Quotient.mk_eq_zero]
    apply hcancel d _ hd
    change d • q (P0 v) = 0
    rw [← map_smul, ← map_smul, show d • v = ((⟨d • v, hv⟩ : L) : V) from rfl, hP0]
    exact (Submodule.Quotient.mk_eq_zero W).2 (hW _)
  · obtain ⟨d, hd, hv⟩ := hden w
    have h0 : qL ⟨d • w, hv⟩ = 0 := by
      apply Subtype.ext
      change q (d • w) = 0
      rw [map_smul]
      change d • (Submodule.Quotient.mk w : V ⧸ W) = 0
      rw [(Submodule.Quotient.mk_eq_zero W).2 hw, smul_zero]
    have h1 : d • P0 w = d • w := by
      rw [← map_smul, show d • w = ((⟨d • w, hv⟩ : L) : V) from rfl, hP0, hp0, h0, map_zero]
      simp
    rw [hP]
    rw [← IsScalarTower.algebraMap_smul K d, ← IsScalarTower.algebraMap_smul K d w] at h1
    exact smul_right_injective V (by simpa using hd) h1
  · rw [hP, show v = ((⟨v, hv⟩ : L) : V) from rfl, hP0, hp0]
    exact L.sub_mem hv (s _).2
end GlobalTheory.DegAsm.FrameMove
