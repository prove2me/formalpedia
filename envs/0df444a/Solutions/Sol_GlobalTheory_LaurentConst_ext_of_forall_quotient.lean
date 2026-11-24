-- Prove2me | solution 1 for GlobalTheory.LaurentConst.ext_of_forall_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:04.798357+00:00
-- url     : https://prove2.me/submissions/9651a300-5f3a-47e3-bcd0-e012201f69fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p] {D : Type} [CommRing D]
    {a b : Spec (.of D) ⟶ Y} (hab : a ≫ p = b ≫ p) (I : ℕ → Ideal D) (hI : ⨅ n, I n = ⊥)
    (H : ∀ n, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n))) ≫ a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n))) ≫ b) : a = b := by
  have := isClosedImmersion_equalizer_ι_of_isSeparated p hab
  have : IsIso (equalizer.ι a b) := by
    refine IsClosedImmersion.isIso_of_injective_of_isAffine ((injective_iff_map_eq_zero _).2 ?_)
    intro x hx
    obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of D)).inv).2 x
    have hd : d ∈ ⨅ n, I n := by
      refine Ideal.mem_iInf.2 fun n ↦ Ideal.Quotient.eq_zero_iff_mem.1 ?_
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (D ⧸ I n))).inv).1
      have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))
      rw [← equalizer.lift_ι _ (H n), Scheme.Hom.comp_appTop] at e
      have e' := congrArg (fun φ ↦ φ.hom d) e
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e'
      rw [map_zero, e', hx, map_zero]
    rw [hI, Ideal.mem_bot] at hd
    rw [hd, map_zero]
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]
end GlobalTheory.LaurentConst
