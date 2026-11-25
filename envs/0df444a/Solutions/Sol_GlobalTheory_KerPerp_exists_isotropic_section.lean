-- Prove2me | solution 1 for GlobalTheory.KerPerp.exists_isotropic_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:33.145302+00:00
-- url     : https://prove2.me/submissions/f5fc01fb-bb9d-4731-8f9b-21a2c0f6d151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSplitOfCoisotropicKer
import Theorems.Thm_GlobalTheory_KerPerp_isotropic
import Theorems.Thm_GlobalTheory_KerPerp_mem_kerPerp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.KerPerp
variable {O L Y : Type} [CommRing O] [StarRing O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {EF : LinearMap.BilinForm ℤ L} {y : L →ₗ[O] Y}
namespace GlobalTheory.KerPerp
theorem _root_.solution [Module.Projective O Y] {w : O} (hw : w + star w = 1) (halt : EF.IsAlt)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ s : Y →ₗ[O] L, (∀ x, y (s x) = x) ∧ ∀ x x', EF (s x) (s x') = 0 := by
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property y LinearMap.id hy
  have hs0' : ∀ x, y (s0 x) = x := fun x => LinearMap.congr_fun hs0 x
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : kerPerp hadj y ≤ LinearMap.ker y := fun t ht => hle t (mem_kerPerp.1 ht)
  obtain ⟨be, hbe_apply⟩ : ∃ be : LinearMap.BilinForm ℤ Y,
      ∀ x x', be x x' = EF (s0 x) (s0 (w • x')) :=
    ⟨EF.compl₁₂ s0.toAddMonoidHom.toIntLinearMap
      (s0.toAddMonoidHom.toIntLinearMap ∘ₗ (LinearMap.lsmul O Y w).toAddMonoidHom.toIntLinearMap),
      fun _ _ => rfl⟩
  have hbe : ∀ (a : O) x x', be (a • x) x' = be x (star a • x') := by
    intro a x x'
    rw [hbe_apply, hbe_apply, map_smul s0 a x, hadj, map_smul s0 w (star a • x'), map_smul s0 w x',
      map_smul s0 (star a) x', smul_comm]
  have hn := neg_apply_nilTo hadj hb hy hbe
  refine ⟨s0 + (kerPerp hadj y).subtype ∘ₗ nilTo hadj hb hy hbe ∘ₗ s0, fun x => ?_, fun x x' => ?_⟩
  · have h0 : y ((nilTo hadj hb hy hbe (s0 x) : L)) = 0 :=
      LinearMap.mem_ker.1 (hle' (nilTo hadj hb hy hbe (s0 x)).2)
    simp [hs0', h0]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add]
    have h1 := hn (s0 x) (s0 x')
    have h2 := hn (s0 x') (s0 x)
    rw [hs0', hs0', hbe_apply] at h1 h2
    have h3 := isotropic hle' (nilTo hadj hb hy hbe (s0 x)).2 (nilTo hadj hb hy hbe (s0 x')).2
    have h4 := skew (s0 x) (nilTo hadj hb hy hbe (s0 x'))
    have k1 : EF (s0 x') (s0 (w • x)) = -EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x, skew, hadj]
    have k2 : EF (s0 x) (s0 x') = EF (s0 x) (s0 (w • x')) + EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x', ← map_add (EF (s0 x)), ← add_smul, hw, one_smul]
    linarith
end GlobalTheory.KerPerp
