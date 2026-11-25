-- Prove2me | solution 1 for GlobalTheory.HL.StabFix.local_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:20.911142+00:00
-- url     : https://prove2.me/submissions/f7251997-0ff6-4b8b-8d6f-a7d7e816b2af

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalCommonStabiliserEqOneOfFixesSecondFrame
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameBasic_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_FrameStab_spanTo_top
import Theorems.Thm_GlobalTheory_HL_FrameStab_stab_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StabFix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.StabFix
theorem _root_.solution (h : S.GLV) (hS : h ∈ S.St) (hf' : ∀ b, h (S.f' b) = S.f' b) : h = 1 := by
  obtain ⟨_, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hW0 := (GlobalTheory.HL.FrameStab.stab_eq L r k S).1 h hS
  have hHe : IsHerm L S.Hm := S.herm.1
  have hN : h ∈ S.N := (Subgroup.mem_inf.1 hS).1
  simp only [Frames.N, Frames.Nof, Subgroup.mem_inf] at hN
  obtain ⟨⟨hiso, -⟩, hU⟩ := hN
  have hiso' : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hiso
  obtain ⟨-, hU2⟩ := hU

  have hfX : ∀ a, S.f a ∈ perp L S.Hm (S.spanTo S.f r) := by
    intro a
    rw [Frames.spanTo, Set.image_eq_range, GlobalTheory.FrameBasic.mem_perp_span L hHe]
    rintro ⟨j, hj⟩
    rw [S.gram]
    have : j ≠ Fin.last r := by
      intro e; simp [e] at hj
    simp [this]
  have hXle : S.spanTo S.f r ≤ S.ME := by
    refine le_trans (Submodule.span_mono (Set.image_mono ?_)) le_sup_left
    intro i hi
    exact Nat.lt_succ_of_lt hi
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    rw [Frames.ME, GlobalTheory.HL.FrameStab.spanTo_top, GlobalTheory.HL.FrameStab.spanTo_top, Set.Sum.elim_range,
      Submodule.span_union]
  have hsub : ∀ a b y, hf L S.Hm (a - b) y = hf L S.Hm a y - hf L S.Hm b y := fun a b y =>
    (GlobalTheory.FrameBasic.hfL L S.Hm y).map_sub a b
  have hfix : ∀ a, h (S.f a) = S.f a := by
    intro a
    have hu : h (S.f a) - S.f a ∈ S.spanTo S.f r := hU2 _ (hfX a)
    have hW : h (S.f a) - S.f a ∈ S.W0 := by
      rw [Frames.W0, hME, GlobalTheory.FrameBasic.mem_perp_span L hHe]
      rintro (i | b)
      · simp only [Sum.elim_inl]
        rw [GlobalTheory.FrameBasic.hf_conj L hHe, hfX i _ hu, map_zero]
      · simp only [Sum.elim_inr]
        rw [hsub, ← hf' b, hiso', hf' b, sub_self]
    have := (Submodule.disjoint_def.1 hcompl.disjoint) _ (hXle hu) hW
    exact sub_eq_zero.1 this
  have hall : ∀ v, h v = v := by
    intro v
    have hv : v ∈ S.ME ⊔ S.W0 := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    have hy' : y ∈ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id := by
      have : S.ME ≤ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id := by
        rw [hME, Submodule.span_le]
        rintro _ ⟨i | b, rfl⟩
        · exact hfix i
        · exact hf' b
      exact this hy
    rw [map_add, hW0 z hz]
    rw [LinearMap.mem_eqLocus] at hy'
    rw [show h y = y from hy']
  exact LinearEquiv.ext hall
end GlobalTheory.HL.StabFix
