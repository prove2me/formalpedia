-- Prove2me | solution 1 for GlobalTheory.nsmulF_add_sqZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:20.78483+00:00
-- url     : https://prove2.me/submissions/79441481-b85f-4ce0-9b47-2c67901267d0

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NsmulFAddSqZeroEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
private lemma fgInv_span_le_nil {S ι : Type} [CommRing S] (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    Ideal.span (Set.range a) ≤ nilradical S := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_nilradical.2 (ha i)
private lemma fgInv_elim_nil {S ι κ : Type} [CommRing S] (a : ι → S) (b : κ → S)
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i, IsNilpotent (Sum.elim a b i) := by
  rintro (i | i)
  · exact ha i
  · exact hb i
private lemma fgInv_det_unit {S : Type} [CommRing S] {g : ℕ} (M : Matrix (Fin g) (Fin g) S)
    (hM : ∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ nilradical S) : IsUnit M.det := by
  have h1 : (Ideal.Quotient.mk (nilradical S)).mapMatrix M =
      (Ideal.Quotient.mk (nilradical S)).mapMatrix 1 := by
    ext k j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (hM k j)
  have h2 : Ideal.Quotient.mk (nilradical S) M.det = Ideal.Quotient.mk (nilradical S) 1 := by
    rw [RingHom.map_det, h1, map_one, Matrix.det_one, map_one]
  have h3 : IsNilpotent (M.det - 1) := mem_nilradical.1 (Ideal.Quotient.eq.1 h2)
  have h4 := h3.isUnit_add_one
  simpa using h4
private lemma fgInv_mulVec_sq {S : Type} [CommRing S] {g : ℕ} (N : Matrix (Fin g) (Fin g) S)
    (e : Fin g → S) (he : ∀ i j, e i * e j = 0) : ∀ i j, (N *ᵥ e) i * (N *ᵥ e) j = 0 := by
  intro i j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  rw [mul_mul_mul_comm, he, mul_zero]
private lemma fgInv_mulVec_eq {S : Type} [CommRing S] {g : ℕ} (M : Matrix (Fin g) (Fin g) S)
    (v u : Fin g → S) (hvu : ∀ i j, v i * u j = 0)
    (hM : ∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range v)) :
    M *ᵥ u = u := by
  have h : (M - 1) *ᵥ u = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have key : ∀ x ∈ Ideal.span (Set.range v), x * u j = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun l _ => by rw [mul_assoc, hvu, mul_zero]
    exact key _ (hM k j)
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) := by
  intro H1 H2 R₀ _ g B K ch n S _ _ hn a e ha he
  have h0 : ∀ i : Fin g, IsNilpotent ((0 : Fin g → S) i) := fun _ => IsNilpotent.zero
  have hnil : ∀ x y : Fin g → S, (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) →
      ∀ i, IsNilpotent (fAdd ch.F x y i) := by
    intro x y hx hy k
    have hxy := fgInv_elim_nil x y hx hy
    have h00 := fgInv_elim_nil (0 : Fin g → S) (0 : Fin g → S) h0 h0
    have e1 := fgInv_span_le_nil _ hxy (((H1 (ch.F k) S (Sum.elim x y)).2 hxy).2)
    have e2 := fgInv_span_le_nil _ h00 (((H1 (ch.F k) S (Sum.elim 0 0)).2 h00).2)
    have e3 : nEval (ch.F k) (Sum.elim (0 : Fin g → S) (0 : Fin g → S)) = 0 :=
      congrFun (ch.F_unit S 0 h0) k
    rw [e3] at e2
    have e4 := (nilradical S).sub_mem e1 e2
    rw [sub_sub_sub_cancel_right, sub_zero] at e4
    exact mem_nilradical.1 e4
  have hns : ∀ x : Fin g → S, (∀ i, IsNilpotent (x i)) → ∀ m,
      ∀ i, IsNilpotent (nsmulF ch.F x m i) := by
    intro x hx m
    induction m with
    | zero => exact h0
    | succ m ih => exact hnil _ _ ih hx
  have hdist : ∀ x y : Fin g → S, (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) → ∀ m,
      nsmulF ch.F (fAdd ch.F x y) m = fAdd ch.F (nsmulF ch.F x m) (nsmulF ch.F y m) := by
    intro x y hx hy m
    induction m with
    | zero => exact (ch.F_unit S 0 h0).symm
    | succ m ih =>
      have hX := hns x hx m
      have hY := hns y hy m
      show fAdd ch.F (nsmulF ch.F (fAdd ch.F x y) m) (fAdd ch.F x y) =
        fAdd ch.F (fAdd ch.F (nsmulF ch.F x m) x) (fAdd ch.F (nsmulF ch.F y m) y)
      rw [ih, ch.F_assoc S _ _ _ hX hY (hnil _ _ hx hy),
        ch.F_assoc S _ _ _ hX hx (hnil _ _ hY hy),
        ← ch.F_assoc S _ _ _ hY hx hy, ← ch.F_assoc S _ _ _ hx hY hy, ch.F_comm S _ _ hY hx]
  obtain ⟨M, hM, hMe⟩ := H2 ch S a ha
  have hdet : IsUnit M.det :=
    fgInv_det_unit M fun k j => fgInv_span_le_nil a ha (hM k j)
  set u : Fin g → S := M⁻¹ *ᵥ e with hu
  have huu : ∀ i j, u i * u j = 0 := fgInv_mulVec_sq _ e he
  have hun : ∀ i, IsNilpotent (u i) := fun i => ⟨2, by rw [pow_two, huu]⟩
  have hau : fAdd ch.F a u = a + e := by
    rw [hMe u huu, hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hmu : ∀ m : ℕ, nsmulF ch.F u m = (m : S) • u := by
    intro m
    induction m with
    | zero => simp [nsmulF]
    | succ m ih =>
      show fAdd ch.F (nsmulF ch.F u m) u = _
      obtain ⟨N, hN, hNe⟩ := H2 ch S (nsmulF ch.F u m) (hns u hun m)
      rw [hNe u huu, fgInv_mulVec_eq N _ u _ hN, ih, Nat.cast_succ, add_smul, one_smul]
      intro i j
      rw [ih, Pi.smul_apply, smul_eq_mul, mul_assoc, huu, mul_zero]
  rw [← hau, hdist a u ha hun, hmu, hn, zero_smul, ch.F_unit S _ (hns a ha n)]
end GlobalTheory
