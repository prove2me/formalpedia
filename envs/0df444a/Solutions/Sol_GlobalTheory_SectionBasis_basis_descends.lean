-- Prove2me | solution 1 for GlobalTheory.SectionBasis.basis_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:05:35.113591+00:00
-- url     : https://prove2.me/submissions/91d27ffc-26f4-43c1-b7b7-dfc3122503e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_SectionBasis_exists_maps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {D N : ℕ} {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
namespace GlobalTheory.SectionBasis
theorem _root_.solution (j0 : ι → Fin (N + 1)) (v : ∀ Z, Fin (N + 1) → Ω Z) (x : ∀ Z, Fin N → Ω Z)
    (hv : ∀ Z, v Z (j0 Z) ≠ 0) (hx : ∀ Z k, x Z k = v Z ((j0 Z).succAbove k) / v Z (j0 Z))
    (hind : ∀ Z, AlgebraicIndependent K (sImg (D := D) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z))))
      (OmS (Ω Z) D N))
    (t : TVar D N → K') (ht : AlgebraicIndependent K t)
    {Q : ι → Type} [∀ Z, CommRing (Q Z)] (a : ∀ Z, K' →+* Q Z) (ψ : ∀ Z, Ω Z →+* Q Z)
    (hc : ∀ Z (c : K), ψ Z (algebraMap K (Ω Z) c) = a Z (algebraMap K K' c))
    (hrel : ∀ Z (i : Fin D), ∑ j, a Z (t (i.succ, j)) * ψ Z (v Z j) = 0)
    (huniv : ∀ Z (R : Type) [CommRing R] (a' : K' →+* R) (ψ' : Ω Z →+* R),
      (∀ c : K, ψ' (algebraMap K (Ω Z) c) = a' (algebraMap K K' c)) → IsUnit (∑ j, a' (t (0, j)) * ψ' (v Z j)) →
      (∀ i : Fin D, ∑ j, a' (t (i.succ, j)) * ψ' (v Z j) = 0) →
      ∃ g : Q Z →+* R, (∀ y, g (a Z y) = a' y) ∧ ∀ ω, g (ψ Z ω) = ψ' ω)
    {n : ℕ} (θ : Fin n → ∀ Z, Ω Z)
    (hli : ∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * ψ Z (θ k Z) = 0) → ∀ k, c k = 0)
    (hsp : ∀ y : ∀ Z, Q Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * ψ Z (θ k Z)) :
    ∑ Z, Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) = n ∧
    (∀ p : Fin n → MvPolynomial (TVar D N) K,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) D N, ∃ q : MvPolynomial (TVar D N) K, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar D N) K, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z)) := by
  classical
  letI iL : ∀ Z, Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) := fun Z =>
    ((algebraMap (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N)).comp
      (hind Z).aevalEquivField.toRingEquiv.toRingHom).toAlgebra
  have hL : ∀ Z (q : MvPolynomial (TVar D N) K), algebraMap (FractionRing (MvPolynomial (TVar D N) K))
      (OmS (Ω Z) D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom (j0 Z) (x Z) q := fun Z q =>
    (hind Z).aevalEquivField_algebraMap_apply_coe q
  have hrk : ∀ Z, Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) =
      Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) :=
    fun Z => Algebra.finrank_eq_of_equiv_equiv (hind Z).aevalEquivField.toRingEquiv (RingEquiv.refl _) rfl
  haveI hfd : ∀ Z, FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) := fun Z => by
    apply Module.finite_of_finrank_pos
    rw [hrk]
    exact Module.finrank_pos
  have hinjt : Function.Injective (aeval t : MvPolynomial (TVar D N) K →ₐ[K] K').toRingHom := ht
  letI iK : Algebra (FractionRing (MvPolynomial (TVar D N) K)) K' :=
    (IsFractionRing.lift (K := FractionRing (MvPolynomial (TVar D N) K)) hinjt).toAlgebra
  have hK : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) K'
      (algebraMap (MvPolynomial (TVar D N) K) _ q) = aeval t q := fun q => IsFractionRing.lift_algebraMap hinjt q
  choose β hβ1 hβ2 α hα1 hα2 using fun Z => exists_maps (j0 Z) (v Z) (x Z) (hv Z) (hx Z) t ht (hL Z) hK (a Z) (ψ Z)
    (hc Z) (hrel Z) (huniv Z)
  have hβF : ∀ Z (y : FractionRing (MvPolynomial (TVar D N) K)), β Z (algebraMap _ _ y) = a Z (algebraMap _ _ y) := by
    intro Z
    have : (β Z).comp (algebraMap (FractionRing (MvPolynomial (TVar D N) K)) _) = (a Z).comp (algebraMap _ _) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (TVar D N) K)) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      rw [hL, hK, hβ1]
    exact fun y => RingHom.congr_fun this y
  let u : Fin n → ∀ Z, OmS (Ω Z) D N := fun k Z => algebraMap (Ω Z) _ (θ k Z)
  have hu : LinearIndependent (FractionRing (MvPolynomial (TVar D N) K)) u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have := hli (fun k => algebraMap _ K' (g k)) (fun Z => by
      have h1 := congrArg (β Z) (congrFun hg Z)
      rw [Finset.sum_apply, map_sum, Pi.zero_apply, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, hβF, hβ2]) k
    exact (map_eq_zero_iff _ (algebraMap _ K').injective).1 this
  have hpi : Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (∀ Z, OmS (Ω Z) D N) =
      ∑ Z, Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) :=
    Module.finrank_pi_fintype _
  have hle : n ≤ Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (∀ Z, OmS (Ω Z) D N) := by
    simpa using hu.fintype_card_le_finrank
  have hge : Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (∀ Z, OmS (Ω Z) D N) ≤ n := by
    let u' : Fin n → ∀ Z, K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS (Ω Z) D N :=
      fun k Z => α Z (ψ Z (θ k Z))
    have hs : Submodule.span K' (Set.range u') = ⊤ := by
      rw [eq_top_iff]
      intro z _
      choose y hy using fun Z => hα2 Z (z Z)
      obtain ⟨c, hc⟩ := hsp y
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨c, funext fun Z => ?_⟩
      rw [← hy, hc, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, hα1]
    have h1 := finrank_le_of_span_eq_top hs
    rw [Module.finrank_pi_fintype, Fintype.card_fin] at h1
    rw [hpi]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun Z _ => ?_)) h1
    rw [Module.finrank_baseChange]
  have heq := le_antisymm hge hle
  have hinj : ∀ Z (q : MvPolynomial (TVar D N) K), sHom (j0 Z) (x Z) q = 0 → q = 0 := fun Z q h =>
    algebraicIndependent_iff.mp (hind Z) q h
  refine ⟨?_, fun p hp k => ?_, fun y => ?_⟩
  · rw [← heq, hpi]
    exact Finset.sum_congr rfl fun Z _ => (hrk Z).symm
  · have := Fintype.linearIndependent_iff.1 hu (fun k => algebraMap _ _ (p k)) (funext fun Z => by
      rw [Finset.sum_apply, Pi.zero_apply, ← hp Z]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, hL]) k
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 this
  · have hs := hu.span_eq_top_of_card_eq_finrank' (by rw [heq, Fintype.card_fin])
    have hy : y ∈ Submodule.span (FractionRing (MvPolynomial (TVar D N) K)) (Set.range u) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (MvPolynomial (TVar D N) K)) c
    choose p hp using hq
    refine ⟨q, fun Z h => nonZeroDivisors.ne_zero q.2 (hinj Z _ h), p, fun Z => ?_⟩
    rw [← hc, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Algebra.smul_def, ← hL, ← hL, hp, Algebra.smul_def, map_mul, mul_assoc]
end GlobalTheory.SectionBasis
