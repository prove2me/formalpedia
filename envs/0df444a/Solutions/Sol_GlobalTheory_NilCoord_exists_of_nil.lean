-- Prove2me | solution 1 for GlobalTheory.NilCoord.exists_of_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:31.167983+00:00
-- url     : https://prove2.me/submissions/b8bb70a3-5147-4e50-9bf4-a28ba5ed28ba

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilCoord
variable {R : Type} [CommRing R] {n : ℕ} {B : Type} [CommRing B] [Algebra R B]
namespace GlobalTheory.NilCoord
theorem _root_.solution (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (e : B →ₐ[R] A) (a : Fin n → A)
    (ha : ∀ j, IsNilpotent (a j)) :
    ∃ φ : B →ₐ[R] A, (∀ b, IsNilpotent (φ b - e b)) ∧
      ∀ j, φ (π (MvPolynomial.X j)) = e (π (MvPolynomial.X j)) + a j := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A :=
    MvPolynomial.aeval (fun j => e (π (MvPolynomial.X j)) + a j)
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (Set.finite_range _)), Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact ha b
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hf₀ : ((Ideal.Quotient.mkₐ R J).comp e).comp π = (Ideal.Quotient.mkₐ R J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin n) R] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ R J).comp e).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  refine ⟨{ φ'.toRingHom with commutes' := fun r => ?_ }, fun b => ?_, fun j => ?_⟩
  · show φ' (algebraMap R B r) = _
    rw [← π.commutes, hc, ρ.commutes]
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (e b) := AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    obtain ⟨N, hN⟩ := hJ
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow e1 N
    rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  · show φ' (π _) = _
    rw [hc]
    exact MvPolynomial.aeval_X _ j
end GlobalTheory.NilCoord
