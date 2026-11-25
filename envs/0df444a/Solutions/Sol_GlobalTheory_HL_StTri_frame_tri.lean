-- Prove2me | solution 1 for GlobalTheory.HL.StTri.frame_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:56:06.261227+00:00
-- url     : https://prove2.me/submissions/36e7a6fd-39bc-4b25-be36-acda6154c33f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
import Theorems.Thm_GlobalTheory_HL_StTri_descend
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StTri
namespace GlobalTheory.HL.StTri
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (xp : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) (hext : A.Ext p x xp)
    (gG : Fin (r + 1) → Fin n → E) (gS : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (u : Fin (r + 1) → (A.loc p).Ep) (hu : ∀ a, IsUnit (u a)) (heq : ∀ a, u a • gS a = A.bc p (gG a))
    (hstep : ∀ j : Fin (r + 1), xp (gS j) - gS j ∈ Submodule.span (A.loc p).Ep (gS '' {i | (i : ℕ) < j})) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, x (gG j) = ∑ i, s i j • gG i := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have key : ∀ j : Fin (r + 1), x (gG j) - gG j ∈ Submodule.span E (gG '' {i | (i : ℕ) < j}) := by
    intro j
    apply descend (A.loc p).ιE gG
    have e1 : (fun i => (A.loc p).ιE ((x (gG j) - gG j) i)) = u j • (xp (gS j) - gS j) := by
      rw [smul_sub, ← map_smul, heq, hext]
      funext i
      simp [Places.bc]
    rw [e1]
    refine Submodule.smul_mem _ _ ?_
    refine (Submodule.span_le.mpr ?_) (hstep j)
    rintro _ ⟨i, hi, rfl⟩
    have h3 : gS i = ((hu i).unit⁻¹ : ((A.loc p).Ep)ˣ) • A.bc p (gG i) := by
      rw [← heq, Units.smul_def, smul_smul, (hu i).val_inv_mul, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have key2 : ∀ j : Fin (r + 1), ∃ l : Fin (r + 1) →₀ E,
      l ∈ Finsupp.supported E E {i : Fin (r + 1) | (i : ℕ) < j} ∧
      Finsupp.linearCombination E gG l = x (gG j) - gG j := fun j =>
    (Finsupp.mem_span_image_iff_linearCombination E).mp (key j)
  choose l hl hl' using key2
  have hz : ∀ i j : Fin (r + 1), ¬ ((i : ℕ) < j) → l j i = 0 := fun i j h =>
    (Finsupp.mem_supported' _ _).mp (hl j) i h
  refine ⟨Matrix.of fun i j => if i = j then 1 else l j i, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp only [Matrix.of_apply, if_neg hne]
    exact hz i j (by rw [Fin.lt_def] at hij; omega)
  · simp
  · have hjj : l j j = 0 := hz j j (lt_irrefl _)
    have hsplit : ∀ i, (if i = j then (1 : E) else l j i) = (if i = j then 1 else 0) + l j i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hjj]
      · simp [h]
    have hlc := hl' j
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
    simp only [Matrix.of_apply, hsplit, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hlc]
    abel
end GlobalTheory.HL.StTri
