-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.ringKrullDim_quotient_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:50.990811+00:00
-- url     : https://prove2.me/submissions/43dd8f74-d305-4c9b-8cb9-dd999deba21a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_finiteType_of_closure
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_trdeg_eq_field


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution {k J A : Type} [Field k] [Fintype J] [CommRing A] [IsDomain A] [Algebra k A]
    (r : J → A) (i : J) (hi : r i = 1)
    (h : Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) = ⊤) (g : ℕ) (hg : ringKrullDim A = g) :
    ringKrullDim (MvPolynomial J k ⧸ RingHom.ker (coneHom (algebraMap k A) r)) = (g + 1 : ℕ) := by
  haveI := finiteType_of_closure r h
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let φ : MvPolynomial J k →ₐ[k] Polynomial A :=
    { coneHom (algebraMap k A) r with commutes' := fun a => by simp [coneHom] }
  let T := φ.range
  have e : (MvPolynomial J k ⧸ RingHom.ker (coneHom (algebraMap k A) r)) ≃+* T :=
    (Ideal.quotientKerEquivRange φ).toRingEquiv
  rw [ringKrullDim_eq_of_ringEquiv e]
  haveI : Algebra.FiniteType k T := Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hX : ∀ j, Polynomial.C (r j) * Polynomial.X ∈ T := fun j => ⟨MvPolynomial.X j, by simp [φ, coneHom]⟩
  have hX1 : (Polynomial.X : Polynomial A) ∈ T := by simpa [hi] using hX i
  haveI : Algebra.IsAlgebraic T (Polynomial A) := by
    have hT : ∀ q ∈ T, IsAlgebraic T q := fun q hq => isAlgebraic_algebraMap (⟨q, hq⟩ : T)
    have hC : ∀ a : A, IsAlgebraic T (Polynomial.C a) := by
      intro a
      have ha : a ∈ Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) := by rw [h]; trivial
      have : Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) ≤
          (Subalgebra.algebraicClosure T (Polynomial A)).toSubring.comap Polynomial.C := by
        rw [Subring.closure_le]
        rintro _ (⟨b, rfl⟩ | ⟨j, rfl⟩)
        · exact hT _ (T.algebraMap_mem b)
        · exact IsAlgebraic.of_mul (y := Polynomial.X) (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero)
            (hT _ hX1) (by rw [mul_comm]; exact hT _ (hX j))
      exact this ha
    refine ⟨fun q => ?_⟩
    induction q using Polynomial.induction_on' with
    | add p q hp hq => exact hp.add hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      exact (hC a).mul ((hT _ hX1).pow n)
  obtain ⟨n, h1, h2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := Polynomial A)
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, hg] at h1
  rw [← trdeg_add_eq k T, trdeg_eq_zero (R := T) (A := Polynomial A), add_zero] at h2
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field n h2, ← h1]
  simp
end GlobalTheory.ZH.ConePrime
