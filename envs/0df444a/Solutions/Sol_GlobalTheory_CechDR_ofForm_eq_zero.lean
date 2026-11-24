-- Prove2me | solution 1 for GlobalTheory.CechDR.ofForm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:41:40.438806+00:00
-- url     : https://prove2.me/submissions/aa08e56f-1533-4207-85a0-c0a0e7257172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
variable {F}
variable (F)
variable {F}
namespace GlobalTheory.CechDR
theorem _root_.solution {ω : Closed1 F} : ofForm F ω = 0 ↔
    ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ T, D R _ (g T) = ω.1.1 T := by
  show Hyp1.mk F (formZZ F ω) = 0 ↔ _
  rw [Hyp1.mk_eq_zero]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · have e : (dTot0 F g).1 T T' φ = 0 := congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ
      rw [dTot0_f] at e
      exact sub_eq_zero.1 e
    · have e : (dTot0 F g).2 T = ω.1.1 T := congrFun (congrArg Prod.snd hg) T
      rw [dTot0_ω] at e
      exact e
  · rintro ⟨g, h1, h2⟩
    refine ⟨g, Prod.ext ?_ ?_⟩
    · funext T T' φ
      show (dTot0 F g).1 T T' φ = 0
      rw [dTot0_f, h1 φ, sub_self]
    · funext T
      show (dTot0 F g).2 T = ω.1.1 T
      rw [dTot0_ω]
      exact h2 T
end GlobalTheory.CechDR
