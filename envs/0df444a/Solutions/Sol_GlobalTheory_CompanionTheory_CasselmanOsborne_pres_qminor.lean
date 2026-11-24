-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.pres_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:09.176061+00:00
-- url     : https://prove2.me/submissions/3a28cc48-6bb9-4a0b-bf41-fbf942f4beba

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_ofFn
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution {n t : ℕ} {R : Submodule ℂ (V × W)} (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (a b : Fin t → Fin n)
    (h : ∀ i j, Pres R (E (a i) (b j)) (F (a i) (b j))) (u : ℂ) :
    Pres R (qminor E a b u) (qminor F a b u) := by
  intro x y hxy
  have key : ∀ σ : Equiv.Perm (Fin t), Pres R
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) *
        (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod)
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) *
        (List.ofFn fun k : Fin t => Tm F (u - (k : ℂ)) (a (σ k)) (b k)).prod) := by
    intro σ
    refine pres_mul ?_ (pres_ofFn _ _ fun k => ?_)
    · intro x y hxy
      have := R.smul_mem (((Equiv.Perm.sign σ : ℤ) : ℂ)) hxy
      simpa [Module.End.intCast_apply, Int.cast_smul_eq_zsmul] using this
    · intro x y hxy
      have h1 := h (σ k) k x y hxy
      unfold Tm
      split_ifs with hc
      · have h2 := R.smul_mem (u - (k : ℂ)) hxy
        have := R.add_mem h2 h1
        exact this
      · simpa using h1
  have := R.sum_mem (t := univ) (fun σ _ => key σ x y hxy)
  unfold qminor
  rw [LinearMap.sum_apply, LinearMap.sum_apply, prod_mk_sum]
  exact this
end GlobalTheory.CompanionTheory.CasselmanOsborne
