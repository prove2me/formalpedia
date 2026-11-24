-- Prove2me | solution 1 for GlobalTheory.BertiniC.no_dependence_of_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:56:02.242855+00:00
-- url     : https://prove2.me/submissions/0f802330-ec4b-4fbd-b822-be7f8e4cd0a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentKaehlerDOfAlgebraicIndependentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelation
import Theorems.Thm_GlobalTheory_BertiniC_false_of_dependent_derivatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BertiniC
open MvPolynomial
namespace GlobalTheory.BertiniC
theorem _root_.solution : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by
  intro k A _ _ _ _ _ n δ ω hω ι _ f M J i₀ p₀ hi₀
  classical
  set I := relIdeal δ f J i₀ p₀ with hIdef
  let T := MvPolynomial (Var M ι) A ⧸ I
  let gm : MvPolynomial (Fin M × ι) k →ₐ[k] T :=
    aeval (fun x => Ideal.Quotient.mk I (X (Sum.inl x)))
  have g1mem : ∀ i ∈ J, (∑ p, X (Sum.inl (i, p)) * C (f p) : MvPolynomial (Var M ι) A) ∈ I :=
    fun i hi => Ideal.subset_span (Or.inl ⟨i, hi, rfl⟩)
  have g2mem : ∀ l, (∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p)) :
      MvPolynomial (Var M ι) A) ∈ I :=
    fun l => Ideal.subset_span (Or.inr (Or.inl ⟨l, rfl⟩))
  have g3mem : (X (Sum.inr (Sum.inl i₀)) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inl rfl)))
  have g4mem : (X (Sum.inr (Sum.inr ())) * C (f p₀) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr rfl)))
  have hni : ¬ Function.Injective gm := by
    intro hinj
    let S : Submonoid T := (nonZeroDivisors (MvPolynomial (Fin M × ι) k)).map gm
    have hS : ∀ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 → gm Q ∈ S := fun Q hQ =>
      Submonoid.mem_map_of_mem _ (mem_nonZeroDivisors_of_ne_zero hQ)
    have hdisj : Disjoint ((⊥ : Ideal T) : Set T) S := by
      rw [Set.disjoint_left]
      rintro x hx ⟨Q, hQ, rfl⟩
      have h0 : gm Q = 0 := (Submodule.mem_bot _).1 hx
      have : Q = 0 := hinj (by rw [h0, map_zero])
      exact nonZeroDivisors.ne_zero hQ this
    obtain ⟨𝔮, h𝔮, -, hd⟩ := Ideal.exists_le_prime_disjoint ⊥ S hdisj
    haveI := h𝔮
    let D := T ⧸ 𝔮
    let κ := FractionRing D
    let π : MvPolynomial (Var M ι) A →+* κ :=
      (algebraMap D κ).comp ((Ideal.Quotient.mk 𝔮).comp (Ideal.Quotient.mk I))
    have hπC : ∀ a : A, π (C a) = algebraMap A κ a := by
      intro a
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I (C a))) = _
      rw [IsScalarTower.algebraMap_apply A D κ]
      rfl
    have hπI : ∀ x ∈ I, π x = 0 := by
      intro x hx
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I x)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
    have ht : AlgebraicIndependent k (fun x : Fin M × ι => π (X (Sum.inl x))) := by
      rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
      intro Q hQ
      by_contra hQ0
      have heq : (aeval (fun x : Fin M × ι => π (X (Sum.inl x))) :
          MvPolynomial (Fin M × ι) k →ₐ[k] κ) =
          (IsScalarTower.toAlgHom k D κ).comp ((Ideal.Quotient.mkₐ k 𝔮).comp gm) := by
        ext x
        simp [π, gm]
      rw [heq] at hQ
      have h1 : Ideal.Quotient.mk 𝔮 (gm Q) = 0 :=
        (IsFractionRing.injective D κ) (hQ.trans (map_zero _).symm)
      rw [Ideal.Quotient.eq_zero_iff_mem] at h1
      exact Set.disjoint_left.1 hd h1 (hS Q hQ0)
    apply false_of_dependent_derivatives n δ ω hω f M J i₀ p₀ hi₀ _ ht (fun i => π (X (Sum.inr (Sum.inl i))))
    · intro i hi
      have := hπI _ (g1mem i hi)
      simpa only [map_sum, map_mul, hπC] using this
    · intro l
      have := hπI _ (g2mem l)
      simpa only [map_sum, map_mul, hπC] using this
    · have h3 : π (X (Sum.inr (Sum.inl i₀)) - 1) = 0 := hπI _ g3mem
      rw [RingHom.map_sub, RingHom.map_one] at h3
      exact h3
    · have h4 := hπI _ g4mem
      rw [RingHom.map_sub, RingHom.map_mul, hπC, RingHom.map_one] at h4
      exact h4
  obtain ⟨Q, hQ0, hQ⟩ : ∃ Q, Q ≠ 0 ∧ gm Q = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hni ((injective_iff_map_eq_zero gm).2 fun Q hQ => by_contra fun h => hcon Q h hQ)
  refine ⟨Q, hQ0, ?_⟩
  intro u hu K _ _ φ c hφ hc hrel hδ
  let e : MvPolynomial (Var M ι) A →+* K := eval₂Hom φ.toRingHom
    (Sum.elim (fun x => algebraMap k K (u x)) (Sum.elim c (fun _ => (φ (f p₀))⁻¹)))
  have hI : I ≤ RingHom.ker e := by
    rw [hIdef, relIdeal, Ideal.span_le]
    rintro x (⟨i, hi, rfl⟩ | ⟨l, rfl⟩ | rfl | rfl) <;> simp only [SetLike.mem_coe, RingHom.mem_ker]
    · have := hrel i hi
      simpa [e, map_sum, Algebra.smul_def] using this
    · have := hδ l
      simpa [e, map_sum, Algebra.smul_def] using this
    · simp [e, hc]
    · simp [e, inv_mul_cancel₀ hφ]
  let e' : T →+* K := Ideal.Quotient.lift I e (fun a ha => hI ha)
  have hcomp : e'.comp gm.toRingHom = (algebraMap k K).comp (eval u) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show e' (gm (C a)) = algebraMap k K (eval u (C a))
      rw [MvPolynomial.aeval_C]
      show e (algebraMap k (MvPolynomial (Var M ι) A) a) = _
      rw [MvPolynomial.algebraMap_apply, eval₂Hom_C, eval_C]
      exact φ.commutes a
    · intro x
      show e' (gm (X x)) = algebraMap k K (eval u (X x))
      rw [MvPolynomial.aeval_X, eval_X]
      show e (X (Sum.inl x)) = _
      rw [eval₂Hom_X']
      rfl
  have := RingHom.congr_fun hcomp Q
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [hQ, map_zero] at this
  exact hu ((algebraMap k K).injective (this.symm.trans (map_zero _).symm))
end GlobalTheory.BertiniC
