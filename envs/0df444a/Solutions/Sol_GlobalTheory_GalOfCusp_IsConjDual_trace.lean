-- Prove2me | solution 1 for GlobalTheory.GalOfCusp.IsConjDual.trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:52:12.66882+00:00
-- url     : https://prove2.me/submissions/00b6cb88-e2ed-4f94-bf98-a8b73d2fb4b2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GalOfCusp
open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {k : Type} [Field k] {a : ℕ}
namespace GlobalTheory.GalOfCusp
namespace IsConjDual
theorem _root_.solution {c : Ω ≃+* Ω} {r : G E Ω →* GL (Fin a) k} {μ : G E Ω →* kˣ} (h : IsConjDual c r μ)
    {g g' : G E Ω} (hg : ∀ x, g' x = c (g (c.symm x))) :
    (r g' : Matrix (Fin a) (Fin a) k).trace = μ g * (r g⁻¹ : Matrix (Fin a) (Fin a) k).trace := by
  obtain ⟨P, hP⟩ := h
  rw [hP g g' hg, Matrix.trace_smul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mul, Matrix.trace_transpose, smul_eq_mul]
end IsConjDual
end GlobalTheory.GalOfCusp
