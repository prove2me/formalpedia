-- Prove2me | solution 1 for GlobalTheory.HL.DatumStab.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:01:08.809805+00:00
-- url     : https://prove2.me/submissions/1fe3bf15-16f9-4dcf-a043-41a7ff2fe694

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers
import Theorems.Thm_GlobalTheory_HL_DatumStab_smul_eq_iff
import Theorems.Thm_GlobalTheory_HL_DatumStab_perp_iff
import Theorems.Thm_GlobalTheory_HL_DatumStab_complementGroup_fixes_frameSpan
import Theorems.Thm_GlobalTheory_HL_DatumStab_X_le
import Theorems.Thm_P2M_GlobalTheory_HL_DatumStab_X__le_b88df43215a7
import Theorems.Thm_GlobalTheory_HL_DatumStab_inner_iff
import Theorems.Thm_GlobalTheory_HL_DatumStab_stab_inner
import Theorems.Thm_GlobalTheory_HL_DatumStab_stab_graph
import Theorems.Thm_GlobalTheory_HL_DatumStab_exists_smul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_StdLat_stdLat_spec
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.DatumStab
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.H0 ⊓ stabL L Λ ≤ S.H0 ⊓ MulAction.stabilizer S.GLV d ∧ ∃ Λ₂ : Submodule L.O S.V, IsLat L Λ₂ ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d ≤ S.H0 ⊓ stabL L Λ₂ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ ⟨⟨n, n'⟩, hI, hI', hn, hn', hΛ, hΛ', _, hg⟩
  obtain ⟨hsd, -, hA⟩ := StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hI
  obtain ⟨-, -, hA'⟩ := StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hI'
  have hc : IsCompl S.ME S.W0 := (FrameBasic.main L r k S).2.1
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  refine ⟨?_, ?_⟩
  · rintro h ⟨hh, hs⟩
    have hs' : h • Λ = Λ := hs
    refine ⟨hh, ?_⟩
    have h1 := inner_iff S hn hA
    have h2 := inner_iff S hn' hA'
    simp only at hΛ hΛ'
    rw [← hΛ] at h1
    rw [← hΛ'] at h2
    change h • d = d
    refine Prod.ext (stab_inner S (X_le S) h1 hh hs') (Prod.ext (stab_inner S (X'_le S) h2 hh hs') ?_)
    change h • d.2.2 = d.2.2
    rw [hg]
    exact stab_graph S hh hs'
  · set Λ₀ := S.stdLat S.f S.es d.1
    let P : S.V →ₗ[E] S.V := S.W0.subtype ∘ₗ Submodule.linearProjOfIsCompl S.W0 S.ME hc.symm
    have hP0 : ∀ x ∈ S.ME, P x = 0 := fun x hx => by
      have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx
      exact congrArg Subtype.val this
    have hP1 : ∀ x ∈ S.W0, P x = x := fun x hx => by
      have := Submodule.linearProjOfIsCompl_apply_left hc.symm ⟨x, hx⟩
      exact congrArg Subtype.val this
    have hME : ∀ x ∈ Set.range S.f ∪ Set.range S.f', x ∈ S.ME := by
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, i.2, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, i.2, rfl⟩)
    refine ⟨(d.1 ⊓ S.W0.restrictScalars L.O) ⊔ Submodule.span L.O (Set.range S.f ∪ Set.range S.f'),
      ⟨Submodule.FG.sup ?_ (Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))), ?_⟩, ?_⟩
    · have hfg : (Λ₀.map (P.restrictScalars L.O)).FG := hsd.1.1.map _
      refine hfg.of_le ?_
      rintro x ⟨hx, hw⟩
      obtain ⟨y, hy, -, hyx⟩ := (hA x).1 hx
      refine ⟨y, hy, ?_⟩
      have := hP0 _ (X_le S hyx)
      rw [map_sub, sub_eq_zero, hP1 x hw] at this
      exact this
    · rw [eq_top_iff, ← hc.sup_eq_top]
      refine sup_le (sup_le ?_ ?_) fun w hw => ?_
      · refine Submodule.span_mono ?_
        rintro _ ⟨i, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
      · refine Submodule.span_mono ?_
        rintro _ ⟨i, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
      · obtain ⟨c, hc0, -, hcw⟩ := exists_smul_mem hsd.1 w
        have hw' := S.W0.smul_mem (algebraMap F E c) hw
        have h1 : algebraMap F E c • w ∈ d.1 :=
          (hA _).2 ⟨_, hcw, fun y hy => hw' y (X_le S hy), by simp⟩
        have h2 : w = algebraMap F E c⁻¹ • algebraMap F E c • w := by
          rw [smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_sup_left ⟨h1, hw'⟩))
    · rintro h ⟨hh, hs⟩
      have hs' : h • d = d := hs
      have h1 : h • d.1 = d.1 := congrArg Prod.fst hs'
      refine ⟨hh, ?_⟩
      change h • _ = _
      rw [Submodule.smul_sup']
      congr 1
      · rw [smul_eq_iff] at h1 ⊢
        intro x
        exact and_congr (h1 x) (perp_iff hh.1 (complementGroup_fixes_frameSpan S hh) x)
      · rw [smul_eq_iff]
        intro x
        have hsub : ∀ z ∈ Submodule.span L.O (Set.range S.f ∪ Set.range S.f'), h z = z := fun z hz =>
          complementGroup_fixes_frameSpan S hh z ((Submodule.span_le.2 hME : _ ≤ S.ME.restrictScalars L.O) hz)
        constructor
        · intro hx
          have := h.injective (hsub _ hx)
          rwa [← this]
        · intro hx
          rwa [hsub x hx]
end GlobalTheory.HL.DatumStab
