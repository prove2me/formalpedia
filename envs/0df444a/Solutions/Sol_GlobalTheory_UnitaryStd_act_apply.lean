-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.act_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:17.894184+00:00
-- url     : https://prove2.me/submissions/2c1b3225-e475-4d54-a56f-5a7c0ae39b36

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open GlobalTheory GlobalTheory.UnitaryStd
variable {r g : ℕ}
variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
variable {ρ g}
variable (ρ g)
theorem _root_.solution (a : 𝓞 E) (x : Lat ρ g) : act ρ g a x = a • x := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_4_1"

end 
