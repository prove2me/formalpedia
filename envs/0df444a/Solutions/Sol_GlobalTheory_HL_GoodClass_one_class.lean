-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.one_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:51.053388+00:00
-- url     : https://prove2.me/submissions/51175252-7276-419a-967d-aa329c8825d6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Theorems.Thm_GlobalTheory_HL_GoodClass_decomp
import Theorems.Thm_GlobalTheory_HL_GoodClass_unit_of_lead
import Theorems.Thm_GlobalTheory_HL_GoodClass_pair_comb
import Theorems.Thm_GlobalTheory_HL_GoodClass_comb_mul
import Theorems.Thm_GlobalTheory_HL_GoodClass_int_mul
import Theorems.Thm_GlobalTheory_HL_GoodClass_up_cT
import Theorems.Thm_GlobalTheory_HL_GoodClass_cT_cT
import Theorems.Thm_GlobalTheory_HL_GoodClass_cT_mul
import Theorems.Thm_GlobalTheory_HL_GoodClass_mem_cls
import Theorems.Thm_GlobalTheory_HL_GoodClass_smul_span_le
import Theorems.Thm_GlobalTheory_HL_GoodClass_int_of_stab
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameClass_frame_classes
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
import Theorems.Thm_GlobalTheory_HL_FrameStab_stab_eq
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.GoodClass
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hg : S.gg = false)
    (hD : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1) :
    S.IsIntCls (S.frameCls S.f S.f') ∧ S.wC (S.frameCls S.f S.f') = 1 ∧
      ∀ C, S.IsIntCls C → ∃ h ∈ S.St, C = h • S.frameCls S.f S.f' := by
  have : Nontrivial E := by
    have := L.free
    exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx =>
    ((GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 x hx).1
  have icT : ∀ {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E}, IsIntM L A → IsIntM L (cT L A) :=
    fun hA i j => hcj _ (hA j i)
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  obtain ⟨hN, hN', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  have hli1 : LinearIndependent E S.f := hli.comp Sum.inl Sum.inl_injective
  have hli2 : LinearIndependent E S.f' := hli.comp Sum.inr Sum.inr_injective
  obtain ⟨σ, hσ, hmono, h0, hu⟩ := unit_of_lead L.O
    (fun x s hs hx => (L.O_def x).2 (IsIntegral.of_pow hs ((L.O_def _).1 hx))) S.w
    (fun b => r - (b : ℕ)) S.Zh (fun a b => S.relevant a b) hD
  have iZ : IsIntM L S.Zh := fun a b => by
    by_cases hb : b = σ a
    · rw [hb]; exact (hu a).1
    · rw [h0 a b hb]; exact L.O.zero_mem
  refine ⟨⟨⟨1, one_mem _, 1, one_mem _, rfl⟩, ?_⟩, ?_, ?_⟩
  · rintro p ⟨A, A', iA, iA', -, -, -, h1, h2⟩ a b
    rw [h1, h2, pair_comb]
    exact int_mul (int_mul (icT iA) iZ) iA' a b
  · have : S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls S.f S.f') = S.K0 := by
      have key : ∀ h ∈ MulAction.stabilizer S.GLV (S.frameCls S.f S.f'),
          h • Submodule.span L.O (Set.range S.f) ≤ Submodule.span L.O (Set.range S.f) ∧
          h • Submodule.span L.O (Set.range S.f') ≤ Submodule.span L.O (Set.range S.f') := by
        intro h hh
        have h1 := (hcls (fun b => h (S.f b)) (fun b => h (S.f' b))).1
        rw [← (hcls S.f S.f').2.2 h, MulAction.mem_stabilizer_iff.1 hh] at h1
        obtain ⟨A, A', iA, iA', -, -, -, h1, h2⟩ := h1
        exact ⟨smul_span_le S _ h iA h1, smul_span_le S _ h iA' h2⟩
      ext h
      simp only [Frames.K0, Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        have k1 := key h h2
        have k2 := key h⁻¹ (inv_mem h2)
        have k3 := smul_mono_right h k2.1
        have k4 := smul_mono_right h k2.2
        rw [smul_inv_smul] at k3 k4
        exact ⟨⟨h1, le_antisymm k1.1 k3⟩, le_antisymm k1.2 k4⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩
        obtain ⟨s, hs, es⟩ := hN h h1.1
        obtain ⟨s', hs', es'⟩ := hN' h h1.2
        rw [MulAction.mem_stabilizer_iff, (hcls S.f S.f').2.2 h]
        exact ((hcls S.f S.f').2.1 (fun b => h (S.f b), fun b => h (S.f' b))
          (mem_cls S hg _ _ _ hs hs' (int_of_stab S _ hli1 h h2 es) (int_of_stab S _ hli2 h h3 es')
            es es')).1
    rw [Frames.wC, this, invVol, Subgroup.relIndex_self]
    simp
  · rintro C ⟨⟨n, hn, n', hn', rfl⟩, hC⟩
    obtain ⟨u, hu1, eu⟩ := hN n hn
    obtain ⟨u', hu1', eu'⟩ := hN' n' hn'
    obtain ⟨D, L₁, V, U₁, hD1, hL₁, hV, hU₁, iL, iU, e1, e2, e3⟩ :=
      decomp L.O S.Zh σ hσ hmono h0 hu (cT L u) u'
        ⟨fun i j h => by simp [cT, hu1.1 i j h], fun i => by simp [cT, hu1.2 i]⟩ hu1' (fun a b => by
          have := hC _ (hcls _ _).1 a b
          simp only [eu, eu'] at this
          rwa [pair_comb] at this)
    obtain ⟨h, hh, eh, eh'⟩ := ((GlobalTheory.HL.FrameStab.stab_eq L r k S).2 (cT L D) V (up_cT L hD1) hV).1
      (by rw [cT_cT, e3])
    refine ⟨h, hh, ?_⟩
    rw [(hcls S.f S.f').2.2 h]
    refine ((hcls _ _).2.1 (fun b => n (S.f b), fun b => n' (S.f' b))
      (mem_cls S hg _ _ _ (up_cT L hL₁) hU₁ (icT iL) iU (fun j => ?_) (fun j => ?_))).1
    · simp only [eh, eu]
      rw [comb_mul, ← cT_mul, ← e1, cT_cT]
    · simp only [eh', eu']
      rw [comb_mul, ← e2]
end GlobalTheory.HL.GoodClass
