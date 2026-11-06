-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_primitive_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:29.576729+00:00
-- url     : https://prove2.me/submissions/91783209-c774-4902-885f-f70f0fff60a0

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_factorsThroughIdeal_iff
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_primitiveOnIdeals_iff_no_descent

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (χ : MulChar R ℂ) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by
  classical
  let : Finite (Ideal R) := Finite.of_injective
    (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  have hbot : FactorsThroughIdeal χ ⊥ := by
    rw [factorsThroughIdeal_iff]
    intro u hu
    have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
    rw [hu1, map_one]
  obtain ⟨I, hI⟩ := (Set.toFinite {I : Ideal R | FactorsThroughIdeal χ I}).exists_maximal
    ⟨⊥, hbot⟩
  obtain ⟨φ, hφ⟩ := hI.1
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  refine ⟨I, φ, hφ, ?_, hI⟩
  apply (primitiveOnIdeals_iff_no_descent φ).mpr
  intro J hJ hdesc
  let K : Ideal R := J.comap (Ideal.Quotient.mk I)
  have hK : FactorsThroughIdeal χ K := by
    apply (factorsThroughIdeal_iff χ K).mpr
    intro u hu
    have huJ : ((quotientUnits I u : (R ⧸ I)ˣ) : R ⧸ I) - 1 ∈ J := by
      change Ideal.Quotient.mk I ((u : R) - 1) ∈ J at hu
      change Ideal.Quotient.mk I (u : R) - 1 ∈ J
      simpa only [map_sub, map_one] using hu
    have heq := congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ
    exact heq.symm.trans ((factorsThroughIdeal_iff φ J).mp hdesc _ huJ)
  have hIK : I ≤ K := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hKI : K ≤ I := hI.2 hK hIK
  apply hJ
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hKI hx)
end OAI.SevenEighths.FiniteConductor
