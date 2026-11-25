-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:10:52.289873+00:00
-- url     : https://prove2.me/submissions/d461b7a0-074a-45b0-8519-c311c9786c42

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Theorems.Thm_GlobalTheory_FinOf_finOf_idem
import Theorems.Thm_GlobalTheory_FinOf_finOf_free
import Theorems.Thm_GlobalTheory_FinOf_finOf_algOf
import Theorems.Thm_GlobalTheory_FinOf_finOf_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
variable (O : LAlg R₀) {A : Type} [CommRing A] [Algebra (O : Type) A] [Algebra R₀ A]
  [IsScalarTower R₀ (O : Type) A]
namespace GlobalTheory.FinOf
theorem _root_.solution (B : BX R₀) (p : ℕ) [Module.Free (O : Type) A] [Module.Finite (O : Type) A]
    (pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S)
    (pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ))
    (pt_p : ∀ S φ, p • pt S φ = 0)
    (pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z)
    (hsep : ∀ f : A, (∀ φ : A →ₐ[(O : Type)] O, φ f = 0) → f = 0)
    (hrank : Module.finrank (O : Type) A = Nat.card (A →ₐ[(O : Type)] O))
    {n : ℕ} (ε : Fin n → A) (hε : CompleteOrthogonalIdempotents ε)
    [hloc : ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})] : Nonempty (FIN B O p) := by
  obtain ⟨hfree, h1⟩ := finOf_free (O := O) ε hε
  have hone : ∀ (S : LAlg R₀) (φ : A →ₐ[R₀] S), ∃ i, φ (ε i) = 1 := by
    intro S φ
    by_contra hcon
    have h0 : ∀ i, φ (ε i) = 0 := fun i =>
      (finOf_idem ((hε.idem i).map φ)).resolve_right fun h => hcon ⟨i, h⟩
    have h1 := congrArg φ hε.complete
    rw [map_sum, map_one, Finset.sum_eq_zero fun i _ => h0 i] at h1
    exact zero_ne_one h1
  have hmk : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε i) = 1 := fun i => by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - ε i})), eq_comm, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton_self _
  refine ⟨FIN.mk (Fin n) (fun i => ⟨A ⧸ Ideal.span {1 - ε i}⟩) (fun i => finOf_sO O _)
    (fun i => ?_) (fun i => pt _ (Ideal.Quotient.mkₐ R₀ _)) (fun i => pt_p _ _)
    (fun S s z hz => ?_) (fun i f hf => ?_) ?_⟩
  · rw [finOf_algOf]
    exact ⟨hfree i, inferInstance⟩
  · obtain ⟨φ, ⟨hφs, hφz⟩, huniq⟩ := pt_univ S s.1 z hz
    obtain ⟨i, hi⟩ := hone S φ
    obtain ⟨ψ, hψs, hψφ⟩ := finOf_lift O (ε i) S s φ hφs hi
    refine ⟨i, ψ, hψs, by rw [pt_nat, hψφ, hφz], fun j φ' h1 h2 => ?_⟩
    have h3 : φ'.1.comp (Ideal.Quotient.mkₐ R₀ _) = φ := by
      refine huniq _ ⟨?_, ?_⟩
      · rw [← h1]; rfl
      · rw [← h2, pt_nat]
    have hj : φ (ε j) = 1 := by
      rw [← h3]
      change φ'.1 (Ideal.Quotient.mk _ (ε j)) = 1
      rw [hmk, map_one]
    have hji : j = i := by
      by_contra hne
      have h4 := congrArg φ (hε.ortho hne)
      rw [map_mul, hi, hj, map_zero, _root_.mul_one] at h4
      exact one_ne_zero h4
    subst hji
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    exact Ideal.Quotient.algHom_ext R₀ (h3.trans hψφ.symm)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
    have h0 : a * ε i = 0 := by
      refine hsep _ fun φ => ?_
      rw [map_mul]
      rcases finOf_idem ((hε.idem i).map φ) with h | h
      · rw [h, mul_zero]
      · obtain ⟨ψ, hψs, hψφ⟩ := finOf_lift O (ε i) O (LHom.id O) (φ.restrictScalars R₀)
          (by ext r; exact φ.commutes r) h
        have h1 := hf ψ hψs
        have h2 : φ a = 0 := (AlgHom.congr_fun hψφ a).symm.trans h1
        rw [h2, zero_mul]
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨a, ?_⟩)
    rw [mul_sub, h0, sub_zero, _root_.mul_one]
  · have h2 : Nat.card (A →ₐ[(O : Type)] O) = Nat.card {t : B.G O // p • t = 0} := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun φ => ⟨pt O (φ.restrictScalars R₀), pt_p _ _⟩) ⟨fun φ φ' h => ?_, fun t => ?_⟩)
      · have h' : pt O (φ.restrictScalars R₀) = pt O (φ'.restrictScalars R₀) :=
          congrArg Subtype.val h
        have := (pt_univ O (AlgHom.id R₀ O) _ (pt_p O (φ'.restrictScalars R₀))).unique
          (y₁ := φ.restrictScalars R₀) (y₂ := φ'.restrictScalars R₀)
          ⟨by ext r; exact φ.commutes r, h'⟩ ⟨by ext r; exact φ'.commutes r, rfl⟩
        exact AlgHom.restrictScalars_injective R₀ this
      · obtain ⟨φ, ⟨h1, h2⟩, -⟩ := pt_univ O (AlgHom.id R₀ O) t.1 t.2
        exact ⟨⟨φ.toRingHom, fun r => AlgHom.congr_fun h1 r⟩, Subtype.ext h2⟩
    rw [← h2, ← hrank, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finOf_algOf]
end GlobalTheory.FinOf
