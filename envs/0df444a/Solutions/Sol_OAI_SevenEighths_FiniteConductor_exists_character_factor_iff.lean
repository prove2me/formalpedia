-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_character_factor_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:50.881939+00:00
-- url     : https://prove2.me/submissions/cc6005e8-4e50-45c2-ab6f-8f532b4b156f

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution {G H : Type*} [Group G] [CommGroup H]
    [Finite H] (q : G →* H) (χ : G →* ℂˣ) :
    (∃ φ : H →* ℂˣ, φ.comp q = χ) ↔ q.ker ≤ χ.ker := by
  constructor
  · rintro ⟨φ, rfl⟩ g hg
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hg, map_one]
  · intro hker
    have hker' : q.rangeRestrict.ker ≤ χ.ker := by
      simpa only [MonoidHom.ker_rangeRestrict] using hker
    let θ : q.range →* ℂˣ :=
      MonoidHom.liftOfSurjective q.rangeRestrict q.rangeRestrict_surjective ⟨χ, hker'⟩
    have hθ : θ.comp q.rangeRestrict = χ := MonoidHom.liftOfRightInverse_comp ..
    obtain ⟨φ, hφ⟩ := MonoidHom.domRestrict_surjective ℂ q.range θ
    refine ⟨φ, ?_⟩
    calc
      φ.comp q = (φ.domRestrict q.range).comp q.rangeRestrict := rfl
      _ = θ.comp q.rangeRestrict := by rw [← hφ]; rfl
      _ = χ := hθ
end OAI.SevenEighths.FiniteConductor
