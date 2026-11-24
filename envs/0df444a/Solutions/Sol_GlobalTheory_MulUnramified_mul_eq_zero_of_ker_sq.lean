-- Prove2me | solution 1 for GlobalTheory.MulUnramified.mul_eq_zero_of_ker_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:25.606034+00:00
-- url     : https://prove2.me/submissions/3fe55acb-003f-40dd-840c-55bda542b6fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified
variable {S : Scheme.{0}}
namespace GlobalTheory.MulUnramified
theorem _root_.solution {R R₀ : CommRingCat.{0}} (φ : R ⟶ R₀) (hφ : RingHom.ker φ.hom ^ 2 = ⊥)
    (W : (Spec R).Opens) (hW : IsAffineOpen W) (s t : Γ(Spec R, W))
    (hs : (Spec.map φ).app W s = 0) (ht : (Spec.map φ).app W t = 0) : s * t = 0 := by
  have h : (Spec.map φ).ker ^ 2 = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    suffices RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ by
      simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
        Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      exact this
    have key : ∀ s ∈ RingHom.ker (Spec.map φ).appTop.hom,
        (Scheme.ΓSpecIso R).hom s ∈ RingHom.ker φ.hom := fun s hs ↦ by
      rw [RingHom.mem_ker] at hs ⊢
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, hs,
        map_zero]
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro s hs t ht
    rw [Ideal.mem_bot]
    apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    rw [map_mul, map_zero, ← Ideal.mem_bot, ← hφ, pow_two]
    exact Ideal.mul_mem_mul (key s hs) (key t ht)
  have h' : RingHom.ker ((Spec.map φ).app W).hom ^ 2 = ⊥ := by
    simpa using congr(($h).ideal ⟨W, hW⟩)
  rw [← Ideal.mem_bot, ← h', pow_two]
  exact Ideal.mul_mem_mul hs ht
end GlobalTheory.MulUnramified
