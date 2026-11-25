-- Prove2me | solution 1 for GlobalTheory.HL.StTri.stab_unitriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:31:56.194039+00:00
-- url     : https://prove2.me/submissions/c83fbe33-c989-47f7-95fe-3190c1c4f500

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
import Theorems.Thm_GlobalTheory_HL_StTri_loc_step
import Theorems.Thm_GlobalTheory_HL_StTri_frame_tri
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
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by
  intro F E _ _ _ _ _ sig A r k G x hx
  obtain ⟨p⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨xp, hxp, hext⟩ := (show ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p x g' from hx) p
  have hxp' := Subgroup.mem_inf.mp hxp
  have hunit : ∀ a : Fin (r + 1), IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := fun a =>
    ((G.c p).isUnit.pow _).map _
  obtain ⟨s, hs, hsx⟩ := frame_tri A p x xp hext G.f (G.S p).f _ hunit (G.f_eq p)
    (loc_step (G.S p) (G.S p).f (fun b hb => by
      rw [(G.S p).gram]
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.1)
  obtain ⟨s', hs', hsx'⟩ := frame_tri A p x xp hext G.f' (G.S p).f' _ hunit (G.f'_eq p)
    (loc_step (G.S p) (G.S p).f' (fun b hb => by
      rw [(G.S p).gram']
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.2)
  exact ⟨s, s', hs, hs', hsx, hsx'⟩
end GlobalTheory.HL.StTri
