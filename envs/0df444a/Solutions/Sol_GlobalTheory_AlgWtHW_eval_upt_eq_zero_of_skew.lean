-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:40.523199+00:00
-- url     : https://prove2.me/submissions/01720c76-b0d2-46e1-a81a-776db6829820

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.AlgWtHW
namespace GlobalTheory.AlgWtHW
theorem _root_.solution (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0)
    (Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) :
    MvPolynomial.eval (upt Y) Q = 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => by simp [hc]
  have hσc : ∀ (σ : L →+* ℂ) x, σ (c x) = ComplexEmbedding.conjugate σ x := fun σ x => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact IsCMField.complexEmbedding_complexConj L σ x

  let B := NumberField.canonicalEmbedding.latticeBasis L
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → L := fun k => NumberField.integralBasis L k
  have hB : ∀ k, B k = fun σ => σ (b k) := fun k => by
    funext σ; rw [NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]
  have H1 : ∀ σ₀ : L →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ,
      ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0 := by
    intro σ₀
    refine ⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩
    have := congrFun (B.sum_repr (Pi.single σ₀ 1)) σ
    simpa [Finset.sum_apply, hB, Pi.single_apply] using this
  choose a ha using H1

  let S : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → Matrix (Fin n) (Fin n) L := fun J =>
    Matrix.of fun u v => (if u = J.1 ∧ v = J.2.1 then b J.2.2 else 0) -
      (if u = J.2.1 ∧ v = J.1 then c (b J.2.2) else 0)
  let r : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → (L →+* ℂ) × Fin n × Fin n → ℂ :=
    fun J => upt (ratPt (S J))
  have hSk : ∀ J u v, S J u v + c (S J v u) = 0 := by
    intro J u v
    simp only [S, Matrix.of_apply, map_sub]
    split_ifs <;> simp only [map_zero, hcc, sub_zero, zero_sub, add_zero, zero_add] <;>
      first | ring1 | (exfalso; tauto)
  have hskew : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (∑ J, (t J : L) • S J) + ((∑ J, (t J : L) • S J).map c)ᵀ = 0 := by
    intro t; ext u v
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast, Matrix.zero_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun J _ => ?_
    rw [← mul_add, hSk, mul_zero]
  have hrat : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (fun p => ∑ J, (t J : ℂ) * r J p) = upt (ratPt (∑ J, (t J : L) • S J)) := by
    intro t; funext p
    simp only [r, upt, ratPt, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, map_ratCast]

  let Q' := MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q
  have heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q := by
    intro z
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext p
    simp [map_sum]
  have hQ' : Q' = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ))
      (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_
    choose t ht using fun J => hz J (Set.mem_univ _)
    have hz' : z = fun J => (t J : ℂ) := by funext J; exact (ht J).symm
    rw [heval, hz', hrat, hQ _ (hskew t), map_zero]

  let z : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ :=
    fun J => (1 / 2) * ∑ σ₀, Y σ₀ J.1 J.2.1 * a σ₀ J.2.2
  have key : ∀ u v (τ : L →+* ℂ), ∑ k, z (u, v, k) * τ (b k) = (1 / 2) * Y τ u v := by
    intro u v τ
    calc ∑ k, z (u, v, k) * τ (b k)
        = ∑ k, ∑ σ₀, (1 / 2) * (Y σ₀ u v * (a σ₀ k * τ (b k))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [z, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          ring
      _ = ∑ σ₀, (1 / 2) * (Y σ₀ u v * ∑ k, a σ₀ k * τ (b k)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = (1 / 2) * Y τ u v := by
          simp only [ha, mul_ite, mul_one, mul_zero]
          simp
  have hcomb : upt Y = fun p => ∑ J, z J * r J p := by
    funext ⟨σ, u, v⟩
    have e1 : ∀ J, r J (σ, u, v) = (if u = J.1 ∧ v = J.2.1 then σ (b J.2.2) else 0) -
        (if u = J.2.1 ∧ v = J.1 then ComplexEmbedding.conjugate σ (b J.2.2) else 0) := by
      intro J
      simp only [r, upt, ratPt, S, Matrix.map_apply, Matrix.of_apply, map_sub]
      simp only [apply_ite σ, map_zero, hσc]
    simp only [e1, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if p = x then if q = x_1 then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    have e3 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if q = x_1 then if p = x then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    rw [e2 (fun x x_1 x_2 => z (x, x_1, x_2) * σ (b x_2)),
      e3 (fun x x_1 x_2 => z (x, x_1, x_2) * (ComplexEmbedding.conjugate σ) (b x_2)), key, key, hY σ]
    simp only [upt, Matrix.neg_apply, Matrix.transpose_apply]
    ring
  rw [hcomb, ← heval, hQ', map_zero]
end GlobalTheory.AlgWtHW
