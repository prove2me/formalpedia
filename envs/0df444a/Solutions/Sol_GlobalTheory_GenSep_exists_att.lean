-- Prove2me | solution 1 for GlobalTheory.GenSep.exists_att
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:30.140605+00:00
-- url     : https://prove2.me/submissions/f9226240-8439-4154-b996-3ab1caed8698

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_GlobalTheory_GenSep_le_lim
import Theorems.Thm_GlobalTheory_GenSep_att_lim
import Theorems.Thm_GlobalTheory_GenSep_le_frc
import Theorems.Thm_GlobalTheory_GenSep_inv_mem_frc
import Theorems.Thm_GlobalTheory_GenSep_att_frc
import Theorems.Thm_GlobalTheory_GenSep_exists_adapted
import Theorems.Thm_GlobalTheory_GenSep_exists_approx
import Theorems.Thm_GlobalTheory_GenSep_OverGauss_gauss
import Theorems.Thm_GlobalTheory_GenSep_OverGauss_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
variable {K' : Type} [Field K'] (φ : MvPolynomial (Fin (D + 1) × Fin N) (la.adicCompletionIntegers K) →+* K')
  (κ : la.adicCompletion K →+* K') (x : Fin N → Ω)
variable {la φ κ x}
namespace GlobalTheory.GenSep
theorem _root_.solution (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    (hφ : ∀ c : K', ∃ a b, φ b ≠ 0 ∧ φ b * c = φ a) (htr : Algebra.trdeg K Ω = D) (hx : ∃ k, x k ≠ 0)
    {F F' : Type} [Field F] [Field F'] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    {w' : AddValuation F' (WithTop ℤ)} {ι' : Ω →+* F'} {e' : K' →+* F'}
    (h : OverGauss la φ κ x w ι e) (h' : OverGauss la φ κ x w' ι' e') (heq : ∀ a, w (ι a) = w' (ι' a)) :
    ∃ A : Subring (F × F'), (∀ z ∈ A, Att w w' ι ι' z) ∧ (∀ a, (ι a, ι' a) ∈ A) ∧ (∀ c, (e c, e' c) ∈ A) ∧
      ∀ y y', (y, y') ∈ A → y ≠ 0 → y' ≠ 0 → (y⁻¹, y'⁻¹) ∈ A := by
  classical
  obtain ⟨j0, hj0, hint⟩ := exists_adapted x hx (w.comap ι)
  have hint1 : ∀ k, 0 ≤ w (ι (x k / x j0)) := hint
  have hint2 : ∀ k, 0 ≤ w' (ι' (x k / x j0)) := fun k => heq _ ▸ hint1 k
  let A₀ : Subring (F × F') :=
    ((eval₂Hom ι (fun p => e (φ (X p)))).prod (eval₂Hom ι' (fun p => e' (φ (X p))))).range
  have hA₀ : ∀ z ∈ A₀, Att w w' ι ι' z := by
    rintro _ ⟨P, rfl⟩
    obtain ⟨g1, g2⟩ := h.gauss hκ htr j0 hj0 hint1 P
    obtain ⟨g3, g4⟩ := h'.gauss hκ htr j0 hj0 hint2 P
    by_cases hQ : aeval (subst x j0) P = 0
    · exact ⟨0, by simp [g1 hQ], by simp [g3 hQ]⟩
    · obtain ⟨α, hα, hmin⟩ := (aeval (subst x j0) P).support.exists_min_image
        (fun β => w (ι ((aeval (subst x j0) P).coeff β))) (MvPolynomial.support_nonempty.2 hQ)
      exact ⟨_, g2 α hα hmin, g4 α hα (fun β hβ => by rw [← heq, ← heq]; exact hmin β hβ)⟩
  have hΩ : ∀ a, (ι a, ι' a) ∈ A₀ := fun a => ⟨C a, by simp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (la.adicCompletionIntegers K)
  have hϖm : ϖ ∈ maximalIdeal (la.adicCompletionIntegers K) := hϖ.not_isUnit
  have hP : ∀ P, (e (φ P), e' (φ P)) ∈ lim w w' A₀ := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C o =>
      intro n
      obtain ⟨a, o', hc⟩ := exists_approx la (o : la.adicCompletion K) (ϖ ^ n.natAbs) (pow_ne_zero _ hϖ.ne_zero)
      refine ⟨_, hΩ (algebraMap K Ω a), ?_, ?_⟩
      · rw [← hκ]; exact h.approx hκ hϖm n hc
      · rw [← hκ]; exact h'.approx hκ hϖm n hc
    | add p q hp hq =>
      have := Subring.add_mem _ hp hq
      simpa only [map_add, Prod.mk_add_mk] using this
    | mul_X p s hp =>
      have := Subring.mul_mem _ hp (le_lim w w' A₀ (⟨X s, by simp⟩ : (e (φ (X s)), e' (φ (X s))) ∈ A₀))
      simpa only [map_mul, Prod.mk_mul_mk] using this
  refine ⟨frc (lim w w' A₀), att_frc w w' ι ι' (att_lim w w' ι ι' heq hA₀),
    fun a => le_frc _ (le_lim w w' A₀ (hΩ a)), fun c => ?_, fun y y' => inv_mem_frc _⟩
  obtain ⟨a, b, hb, hc⟩ := hφ c
  refine ⟨_, hP b, (map_ne_zero e).2 hb, (map_ne_zero e').2 hb, ?_⟩
  rw [Prod.mk_mul_mk, ← map_mul, ← map_mul, hc]
  exact hP a
end GlobalTheory.GenSep
