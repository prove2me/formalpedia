-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4ab82969-1979-5ba0-b87f-ca52c968cc4d

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker

namespace TorusRecursion

open LanglandsTunnell.CubicInduction
open scoped WithZero

section Balls

private theorem isOpen_closedBall_zero (v : HeightOneSpectrum (𝓞 ℚ)) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ γ} := by
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective (K := ℚ) (v := v) γ
  have hpos : (0 : ℤᵐ⁰) < Valued.v y := zero_lt_iff.mpr hγ
  have hr : (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰).restrict y ≠ 0 :=
    ((Valuation.restrict_pos_iff (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰) y).mpr hpos).ne'
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ Valued.v y} =
      {x : v.adicCompletion ℚ | (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰).restrict x ≤
        (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰).restrict y} := by
    ext x
    exact Valuation.isEquiv_restrict (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰) x y
  rw [hset]
  exact Valued.isOpen_closedBall (v.adicCompletion ℚ) hr

end Balls

section Congruence

private theorem valued_sum_mul_le (v : HeightOneSpectrum (𝓞 ℚ)) (x y : Fin 3 → v.adicCompletion ℚ)
    (ε : ℤᵐ⁰) (hx : ∀ l, Valued.v (x l) ≤ 1) (hy : ∀ l, Valued.v (y l) ≤ ε) :
    Valued.v (∑ l : Fin 3, x l * y l) ≤ ε := by
  have hterm : ∀ l, Valued.v (x l * y l) ≤ ε := fun l => by
    rw [Valuation.map_mul]
    calc Valued.v (x l) * Valued.v (y l) ≤ 1 * ε := mul_le_mul' (hx l) (hy l)
      _ = ε := one_mul ε
  rw [Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private def congrSubgroup (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
    ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(c : ℤ))}
  one_mem' := by
    refine ⟨one_mem _, fun i j => ?_⟩
    simp only [Units.val_one, sub_self, Valuation.map_zero, zero_le']
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun i j => ?_⟩
    have hsplit : ((a * b : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
        (∑ l : Fin 3, (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i l *
          ((b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l j -
            (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l j)) +
        ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) := by
      rw [Units.val_mul, Matrix.mul_apply]
      simp only [Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [hsplit]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (ha' i j))
    exact valued_sum_mul_le v _ _ _ (fun l => ha.1 i l) (fun l => hb' l j)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun i j => ?_⟩
    have hsplit : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
        ∑ l : Fin 3, ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i l *
          (- ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l j -
            (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l j)) := by
      have h1 : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = 1 := a.inv_mul
      have h2 := congrFun (congrFun h1 i) j
      rw [Matrix.mul_apply] at h2
      simp only [Matrix.one_apply, mul_neg, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h2]
      ring
    rw [hsplit]
    refine valued_sum_mul_le v _ _ _ (fun l => ha.2 i l) (fun l => ?_)
    rw [Valuation.map_neg]
    exact ha' l j

private theorem mem_congrSubgroup_iff (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) (k : LocalGL3 v) :
    k ∈ congrSubgroup v c ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(c : ℤ)) :=
  Iff.rfl

private theorem congrSubgroup_anti (v : HeightOneSpectrum (𝓞 ℚ)) {c c' : ℕ} (h : c ≤ c') :
    congrSubgroup v c' ≤ congrSubgroup v c := by
  intro k hk
  refine ⟨hk.1, fun i j => le_trans (hk.2 i j) ?_⟩
  exact WithZero.exp_le_exp.mpr (by omega)

private theorem continuous_matrixEntry (v : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 3) :
    Continuous fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
  Units.continuous_val.matrix_elem i j

private theorem continuous_inv_entry (v : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 3) :
    Continuous fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
  Units.continuous_coe_inv.matrix_elem i j

private theorem isOpen_localMaximalCompact3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hball : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ (1 : ℤᵐ⁰)} := isOpen_closedBall_zero v one_ne_zero
  have hset : ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹'
        {x | Valued.v x ≤ 1}) ∩
      (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : LocalGL3 v =>
        ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹' {x | Valued.v x ≤ 1}) := by
    ext k
    simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_setOf_eq]
  rw [hset]
  refine IsOpen.inter ?_ ?_ <;> refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  · exact hball.preimage (continuous_matrixEntry v i j)
  · exact hball.preimage (continuous_inv_entry v i j)

private theorem isOpen_congrSubgroup (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) :
    IsOpen ((congrSubgroup v c : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hball : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(c : ℤ))} :=
    isOpen_closedBall_zero v WithZero.exp_ne_zero
  have hset : ((congrSubgroup v c : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) ∩
      ⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹' {x | Valued.v x ≤ WithZero.exp (-(c : ℤ))} := by
    ext k
    simp only [SetLike.mem_coe, mem_congrSubgroup_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_setOf_eq]
  rw [hset]
  refine (isOpen_localMaximalCompact3 v).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact hball.preimage ((continuous_matrixEntry v i j).sub continuous_const)

end Congruence

section Residues

private abbrev Res (v : HeightOneSpectrum (𝓞 ℚ)) : Type := IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)

private noncomputable scoped instance fintypeRes (v : HeightOneSpectrum (𝓞 ℚ)) : Fintype (Res v) := Fintype.ofFinite _

private noncomputable def lift (v : HeightOneSpectrum (𝓞 ℚ)) (r : Res v) : v.adicCompletionIntegers ℚ :=
  Function.surjInv (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers ℚ)) r

private theorem residue_lift (v : HeightOneSpectrum (𝓞 ℚ)) (r : Res v) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) (lift v r) = r :=
  Function.surjInv_eq (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers ℚ)) r

private noncomputable def rep (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ) (c : ℕ) (r : Res v) :
    v.adicCompletion ℚ :=
  algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ c *
    algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (lift v r)

private theorem valued_rep_le (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (c : ℕ) (r : Res v) : Valued.v (rep v ϖ c r) ≤ WithZero.exp (-(c : ℤ)) := by
  unfold rep
  rw [Valuation.map_mul, Valuation.map_pow, hϖ]
  calc WithZero.exp (-1 : ℤ) ^ c * Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (lift v r))
      ≤ WithZero.exp (-1 : ℤ) ^ c * 1 := mul_le_mul_right (lift v r).2 _
    _ = WithZero.exp (-(c : ℤ)) := by rw [mul_one, ← WithZero.exp_nsmul]; congr 1; simp

end Residues

section Invariance

private theorem valued_add_le (v : HeightOneSpectrum (𝓞 ℚ)) {x y : v.adicCompletion ℚ} {ε : ℤᵐ⁰}
    (hx : Valued.v x ≤ ε) (hy : Valued.v y ≤ ε) : Valued.v (x + y) ≤ ε :=
  le_trans (Valuation.map_add _ _ _) (max_le hx hy)

private theorem valued_neg_le (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ} {ε : ℤᵐ⁰}
    (hx : Valued.v x ≤ ε) : Valued.v (-x) ≤ ε := by
  rw [Valuation.map_neg]
  exact hx

private theorem valued_sub_le (v : HeightOneSpectrum (𝓞 ℚ)) {x y : v.adicCompletion ℚ} {ε : ℤᵐ⁰}
    (hx : Valued.v x ≤ ε) (hy : Valued.v y ≤ ε) : Valued.v (x - y) ≤ ε := by
  rw [sub_eq_add_neg]
  exact valued_add_le v hx (valued_neg_le v hy)

private theorem valued_mul_le_left (v : HeightOneSpectrum (𝓞 ℚ)) {x y : v.adicCompletion ℚ} {ε : ℤᵐ⁰}
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ ε) : Valued.v (x * y) ≤ ε := by
  rw [Valuation.map_mul]
  calc Valued.v x * Valued.v y ≤ 1 * ε := mul_le_mul' hx hy
    _ = ε := one_mul ε

private theorem valued_mul_le_right (v : HeightOneSpectrum (𝓞 ℚ)) {x y : v.adicCompletion ℚ} {ε : ℤᵐ⁰}
    (hx : Valued.v x ≤ ε) (hy : Valued.v y ≤ 1) : Valued.v (x * y) ≤ ε := by
  rw [mul_comm]
  exact valued_mul_le_left v hy hx

private theorem valued_mul_le_deeper (v : HeightOneSpectrum (𝓞 ℚ)) {x y : v.adicCompletion ℚ} {c : ℕ} (hc : 1 ≤ c)
    (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) (hy : Valued.v y ≤ WithZero.exp (-(c : ℤ))) :
    Valued.v (x * y) ≤ WithZero.exp (-(c : ℤ) - 1) := by
  rw [Valuation.map_mul]
  calc Valued.v x * Valued.v y ≤ WithZero.exp (-(c : ℤ)) * WithZero.exp (-(c : ℤ)) := mul_le_mul' hx hy
    _ = WithZero.exp (-(c : ℤ) + -(c : ℤ)) := (WithZero.exp_add _ _).symm
    _ ≤ WithZero.exp (-(c : ℤ) - 1) := WithZero.exp_le_exp.mpr (by omega)

private theorem exp_deeper_le (c : ℕ) : WithZero.exp (-(c : ℤ) - 1) ≤ WithZero.exp (-(c : ℤ)) :=
  WithZero.exp_le_exp.mpr (by omega)

private theorem exp_neg_natCast_le_one (n : ℕ) : WithZero.exp (-(n : ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by omega)

private theorem valued_le_exp_neg_one_of_lt_one {γ : ℤᵐ⁰} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero] at h
    exact WithZero.exp_le_exp.mpr (by have := WithZero.exp_lt_exp.mp h; omega)

private theorem valued_uniformizer_pow (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (c : ℕ) : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ c) =
      WithZero.exp (-(c : ℤ)) := by
  rw [Valuation.map_pow, hϖ, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem valued_uniformizer_inv_pow (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (c : ℕ) : Valued.v ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ ^ c) =
      WithZero.exp (c : ℤ) := by
  rw [Valuation.map_pow, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem valued_integral_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletionIntegers ℚ) :
    Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) x) ≤ 1 :=
  x.2

private theorem algebraMap_integers_eq_coe (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletionIntegers ℚ) :
    algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) x = (x : v.adicCompletion ℚ) :=
  rfl

private theorem coe_integers_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) : (ϖ : v.adicCompletion ℚ) ≠ 0 := by
  rw [← algebraMap_integers_eq_coe v ϖ]
  exact hπ

private noncomputable def resOf (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ 1) :
    Res v :=
  IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨x, hx⟩

private theorem valued_quot_le_one (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) :
    Valued.v (x * (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ ^ c) ≤ 1 := by
  rw [Valuation.map_mul, valued_uniformizer_inv_pow v hϖ c]
  calc Valued.v x * WithZero.exp (c : ℤ) ≤ WithZero.exp (-(c : ℤ)) * WithZero.exp (c : ℤ) :=
        mul_le_mul_left hx _
    _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

private theorem valued_rep_add_sub_rep_add (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (c : ℕ) (a : Res v) {e : v.adicCompletion ℚ} (he : Valued.v e ≤ WithZero.exp (-(c : ℤ))) :
    Valued.v (rep v ϖ c a + e - rep v ϖ c (a + resOf v _ (valued_quot_le_one v hϖ he))) ≤
      WithZero.exp (-(c : ℤ) - 1) := by
  obtain ⟨q, hq⟩ : ∃ q : v.adicCompletionIntegers ℚ,
      q = ⟨e * (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ ^ c,
        valued_quot_le_one v hϖ he⟩ := ⟨_, rfl⟩
  have hqres : resOf v _ (valued_quot_le_one v hϖ he) = IsLocalRing.residue (v.adicCompletionIntegers ℚ) q := by
    subst hq
    rfl
  have he' : e = algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ c *
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) q := by
    subst hq
    show e = _ ^ c * (e * _⁻¹ ^ c)
    rw [inv_pow, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero c hπ), mul_one]
  obtain ⟨d, hd⟩ : ∃ d : v.adicCompletionIntegers ℚ,
      d = lift v a + q - lift v (a + resOf v _ (valued_quot_le_one v hϖ he)) := ⟨_, rfl⟩
  have hres : IsLocalRing.residue (v.adicCompletionIntegers ℚ) d = 0 := by
    rw [hd, map_sub, map_add, residue_lift, residue_lift, hqres]
    exact sub_self _
  have hmem : Valued.v (d : v.adicCompletion ℚ) ≤ WithZero.exp (-1 : ℤ) := by
    refine valued_le_exp_neg_one_of_lt_one ?_
    rw [IsLocalRing.residue_eq_zero_iff] at hres
    exact (NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 ℚ) ℚ v d).mp hres
  have hid : rep v ϖ c a + e - rep v ϖ c (a + resOf v _ (valued_quot_le_one v hϖ he)) =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ c *
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) d := by
    rw [hd]
    simp only [rep]
    rw [map_sub, map_add, mul_sub, mul_add, ← he']
  rw [hid, Valuation.map_mul, valued_uniformizer_pow v hϖ c, algebraMap_integers_eq_coe v d]
  calc WithZero.exp (-(c : ℤ)) * Valued.v (d : v.adicCompletion ℚ)
      ≤ WithZero.exp (-(c : ℤ)) * WithZero.exp (-1 : ℤ) := mul_le_mul_right hmem _
    _ = WithZero.exp (-(c : ℤ) - 1) := by rw [← WithZero.exp_add, sub_eq_add_neg]

private theorem coe_gen₁ (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) :
    ((iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagZ, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem gen₁_mul_gen₁_neg (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) :
    (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v) *
      iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (-1)) = 1 := by
  have hπ' := coe_integers_ne_zero v hπ
  rw [← map_mul, ← map_one iotaGL]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, hπ']

private theorem coe_gen₁_inv (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) :
    (((iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v)⁻¹ :
      LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [inv_eq_of_mul_eq_one_right (gen₁_mul_gen₁_neg v ϖ hπ), coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagZ, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem coe_conj₁ (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (m : LocalGL3 v) :
    ((((iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v)⁻¹ * m *
        iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0,
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ *
            (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1,
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ *
            (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2;
        (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 *
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2;
        (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 *
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2] := by
  rw [Units.val_mul, Units.val_mul, coe_gen₁, coe_gen₁_inv]
  have hπ' := coe_integers_ne_zero v hπ
  have key : ∀ x : v.adicCompletion ℚ, (ϖ : v.adicCompletion ℚ)⁻¹ * x * ϖ = x := fun x => by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ', one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, key, hπ']

private theorem valued_off_le (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℕ} {k : LocalGL3 v} (hk : k ∈ congrSubgroup v c)
    {i j : Fin 3} (hij : i ≠ j) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(c : ℤ)) := by
  simpa [Matrix.one_apply_ne hij] using hk.2 i j

private theorem valued_diag_le (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℕ} {k : LocalGL3 v} (hk : k ∈ congrSubgroup v c)
    (i : Fin 3) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i i - 1) ≤ WithZero.exp (-(c : ℤ)) := by
  simpa using hk.2 i i

private theorem valued_entry_le (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℕ} {k : LocalGL3 v} (hk : k ∈ congrSubgroup v c)
    (i j : Fin 3) : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 :=
  hk.1.1 i j

private theorem conj₁_mem_congrSubgroup (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} (hc : 1 ≤ c) {m : LocalGL3 v} (hm : m ∈ congrSubgroup v c)
    (h01 : Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1) ≤ WithZero.exp (-(c : ℤ) - 1))
    (h02 : Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2) ≤ WithZero.exp (-(c : ℤ) - 1)) :
    (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v)⁻¹ * m *
      iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) ∈ congrSubgroup v c := by
  have hmi : m⁻¹ ∈ congrSubgroup v c := inv_mem hm
  have hϖ1 : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≤ 1 := by
    rw [hϖ, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hϖinv : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ = WithZero.exp (1 : ℤ) := by
    rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]

  have hdeep : ∀ {x : v.adicCompletion ℚ}, Valued.v x ≤ WithZero.exp (-(c : ℤ) - 1) →
      Valued.v ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ * x) ≤ WithZero.exp (-(c : ℤ)) := by
    intro x hx
    rw [Valuation.map_mul, hϖinv]
    calc WithZero.exp (1 : ℤ) * Valued.v x ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-(c : ℤ) - 1) :=
          mul_le_mul_right hx _
      _ = WithZero.exp (-(c : ℤ)) := by rw [← WithZero.exp_add]; congr 1; ring
  have hint : ∀ {x : v.adicCompletion ℚ}, Valued.v x ≤ WithZero.exp (-(c : ℤ)) →
      Valued.v ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ * x) ≤ 1 := by
    intro x hx
    rw [Valuation.map_mul, hϖinv]
    calc WithZero.exp (1 : ℤ) * Valued.v x ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-(c : ℤ)) := mul_le_mul_right hx _
      _ = WithZero.exp (1 - (c : ℤ)) := by rw [← WithZero.exp_add, sub_eq_add_neg]
      _ ≤ 1 := by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)
  have hright : ∀ {x : v.adicCompletion ℚ} {ε : ℤᵐ⁰}, Valued.v x ≤ ε →
      Valued.v (x * algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≤ ε :=
    fun hx => valued_mul_le_right v hx hϖ1
  have hconj_inv : ((iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) :
      LocalGL3 v)⁻¹ * m * iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1))⁻¹ =
      (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v)⁻¹ * m⁻¹ *
        iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) := by
    group
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [coe_conj₁]
    fin_cases i <;> fin_cases j
    · simpa using valued_entry_le v hm 0 0
    · simpa using hint (le_trans h01 (exp_deeper_le c))
    · simpa using hint (le_trans h02 (exp_deeper_le c))
    · simpa using hright (valued_entry_le v hm 1 0)
    · simpa using valued_entry_le v hm 1 1
    · simpa using valued_entry_le v hm 1 2
    · simpa using hright (valued_entry_le v hm 2 0)
    · simpa using valued_entry_le v hm 2 1
    · simpa using valued_entry_le v hm 2 2
  · rw [hconj_inv, coe_conj₁]
    fin_cases i <;> fin_cases j
    · simpa using valued_entry_le v hmi 0 0
    · simpa using hint (valued_off_le v hmi (by decide : (0 : Fin 3) ≠ 1))
    · simpa using hint (valued_off_le v hmi (by decide : (0 : Fin 3) ≠ 2))
    · simpa using hright (valued_entry_le v hmi 1 0)
    · simpa using valued_entry_le v hmi 1 1
    · simpa using valued_entry_le v hmi 1 2
    · simpa using hright (valued_entry_le v hmi 2 0)
    · simpa using valued_entry_le v hmi 2 1
    · simpa using valued_entry_le v hmi 2 2
  · rw [coe_conj₁]
    fin_cases i <;> fin_cases j
    · simpa using valued_diag_le v hm 0
    · simpa using hdeep h01
    · simpa using hdeep h02
    · simpa using hright (valued_off_le v hm (by decide : (1 : Fin 3) ≠ 0))
    · simpa using valued_diag_le v hm 1
    · simpa using valued_off_le v hm (by decide : (1 : Fin 3) ≠ 2)
    · simpa using hright (valued_off_le v hm (by decide : (2 : Fin 3) ≠ 0))
    · simpa using valued_off_le v hm (by decide : (2 : Fin 3) ≠ 1)
    · simpa using valued_diag_le v hm 2

end Invariance

section Translation

private theorem coe_upperUnipotent3_inv (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ) :
    (((upperUnipotent3 x y z : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl

private theorem valued_le_one_of_le_exp_neg (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ} {c : ℕ}
    (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) : Valued.v x ≤ 1 :=
  le_trans hx (exp_neg_natCast_le_one c)

private theorem upperUnipotent3_mem_congrSubgroup (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℕ} {x y z : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) (hy : Valued.v y ≤ WithZero.exp (-(c : ℤ)))
    (hz : Valued.v z ≤ WithZero.exp (-(c : ℤ))) : (upperUnipotent3 x y z : LocalGL3 v) ∈ congrSubgroup v c := by
  have hx1 := valued_le_one_of_le_exp_neg v hx
  have hy1 := valued_le_one_of_le_exp_neg v hy
  have hz1 := valued_le_one_of_le_exp_neg v hz
  have hxy : Valued.v (x * y - z) ≤ 1 := valued_sub_le v (valued_mul_le_left v hx1 hy1) hz1
  have hx' : Valued.v x ≤ (WithZero.exp (c : ℤ))⁻¹ := by rwa [WithZero.exp_neg] at hx
  have hy' : Valued.v y ≤ (WithZero.exp (c : ℤ))⁻¹ := by rwa [WithZero.exp_neg] at hy
  have hz' : Valued.v z ≤ (WithZero.exp (c : ℤ))⁻¹ := by rwa [WithZero.exp_neg] at hz
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx1, hy1, hz1]
  · rw [coe_upperUnipotent3_inv]
    fin_cases i <;> fin_cases j <;> simp [hx1, hy1, hxy]
  · rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx', hy', hz']

private noncomputable def shift₁ (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} {k : LocalGL3 v} (hk : k ∈ congrSubgroup v c) : Res v × Res v :=
  (resOf v _ (valued_quot_le_one v hϖ (valued_off_le v hk (by decide : (0 : Fin 3) ≠ 1))),
    resOf v _ (valued_quot_le_one v hϖ (valued_off_le v hk (by decide : (0 : Fin 3) ≠ 2))))

private theorem translate₁ (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} (hc : 1 ≤ c) {k : LocalGL3 v} (hk : k ∈ congrSubgroup v c) (i : Res v × Res v) :
    let m : LocalGL3 v := (upperUnipotent3 (rep v ϖ c (i + shift₁ v hϖ hk).1) 0 (rep v ϖ c (i + shift₁ v hϖ hk).2) :
      LocalGL3 v)⁻¹ * k * upperUnipotent3 (rep v ϖ c i.1) 0 (rep v ϖ c i.2)
    m ∈ congrSubgroup v c ∧
      Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1) ≤ WithZero.exp (-(c : ℤ) - 1) ∧
      Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2) ≤ WithZero.exp (-(c : ℤ) - 1) := by
  intro m

  have hx := valued_rep_le v hϖ c i.1
  have hz := valued_rep_le v hϖ c i.2
  have hx' := valued_rep_le v hϖ c (i + shift₁ v hϖ hk).1
  have hz' := valued_rep_le v hϖ c (i + shift₁ v hϖ hk).2
  have hx'1 := valued_le_one_of_le_exp_neg v hx'
  have hz'1 := valued_le_one_of_le_exp_neg v hz'
  have hzero : Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp (-(c : ℤ)) := by simp
  refine ⟨mul_mem (mul_mem (inv_mem (upperUnipotent3_mem_congrSubgroup v hx' hzero hz')) hk)
    (upperUnipotent3_mem_congrSubgroup v hx hzero hz), ?_, ?_⟩
  ·
    have hid : (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 =
        ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 - 1) * rep v ϖ c i.1 +
          (rep v ϖ c i.1 + (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 -
            rep v ϖ c (i + shift₁ v hϖ hk).1) +
          (-(rep v ϖ c (i + shift₁ v hϖ hk).1 * ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 - 1))) +
          (-(rep v ϖ c (i + shift₁ v hϖ hk).1 *
            ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * rep v ϖ c i.1))) +
          (-(rep v ϖ c (i + shift₁ v hϖ hk).2 *
            ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 * rep v ϖ c i.1 +
              (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1))) := by
      simp only [m, Units.val_mul, coe_upperUnipotent3_inv, upperUnipotent3_coe, Matrix.mul_apply,
        Fin.sum_univ_three]
      simp
      ring
    have hshift : (i + shift₁ v hϖ hk).1 = i.1 + resOf v _ (valued_quot_le_one v hϖ
        (valued_off_le v hk (by decide : (0 : Fin 3) ≠ 1))) := rfl
    rw [hid]
    refine valued_add_le v (valued_add_le v (valued_add_le v (valued_add_le v ?_ ?_) ?_) ?_) ?_
    · exact valued_mul_le_deeper v hc (valued_diag_le v hk 0) hx
    · rw [hshift]
      exact valued_rep_add_sub_rep_add v hπ hϖ c i.1 (valued_off_le v hk (by decide))
    · exact valued_neg_le v (valued_mul_le_deeper v hc hx' (valued_diag_le v hk 1))
    · exact valued_neg_le v (valued_mul_le_left v hx'1
        (valued_mul_le_deeper v hc (valued_off_le v hk (by decide)) hx))
    · exact valued_neg_le v (valued_mul_le_deeper v hc hz'
        (valued_add_le v (valued_mul_le_left v (valued_entry_le v hk 2 0) hx) (valued_off_le v hk (by decide))))
  ·
    have hid : (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 =
        ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 - 1) * rep v ϖ c i.2 +
          (rep v ϖ c i.2 + (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 -
            rep v ϖ c (i + shift₁ v hϖ hk).2) +
          (-(rep v ϖ c (i + shift₁ v hϖ hk).1 *
            ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * rep v ϖ c i.2 +
              (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2))) +
          (-(rep v ϖ c (i + shift₁ v hϖ hk).2 *
            ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 * rep v ϖ c i.2))) +
          (-(rep v ϖ c (i + shift₁ v hϖ hk).2 * ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 - 1))) := by
      simp only [m, Units.val_mul, coe_upperUnipotent3_inv, upperUnipotent3_coe, Matrix.mul_apply,
        Fin.sum_univ_three]
      simp
      ring
    have hshift : (i + shift₁ v hϖ hk).2 = i.2 + resOf v _ (valued_quot_le_one v hϖ
        (valued_off_le v hk (by decide : (0 : Fin 3) ≠ 2))) := rfl
    rw [hid]
    refine valued_add_le v (valued_add_le v (valued_add_le v (valued_add_le v ?_ ?_) ?_) ?_) ?_
    · exact valued_mul_le_deeper v hc (valued_diag_le v hk 0) hz
    · rw [hshift]
      exact valued_rep_add_sub_rep_add v hπ hϖ c i.2 (valued_off_le v hk (by decide))
    · exact valued_neg_le v (valued_mul_le_deeper v hc hx'
        (valued_add_le v (valued_mul_le_left v (valued_entry_le v hk 1 0) hz) (valued_off_le v hk (by decide))))
    · exact valued_neg_le v (valued_mul_le_left v hz'1
        (valued_mul_le_deeper v hc (valued_off_le v hk (by decide)) hz))
    · exact valued_neg_le v (valued_mul_le_deeper v hc hz' (valued_diag_le v hk 2))

end Translation

section SecondOperator

private theorem coe_gen₂ (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) :
    ((iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ, 0, 0;
        0, algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ, 0; 0, 0, 1] := by
  rw [coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem gen₂_mul_gen₂_inv (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) :
    (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v) *
      iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ (inv_ne_zero hπ)) = 1 := by
  have hπ' := coe_integers_ne_zero v hπ
  rw [← map_mul, ← map_one iotaGL]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, hπ']

private theorem coe_gen₂_inv (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) :
    (((iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v)⁻¹ :
      LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹, 0, 0;
        0, (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹, 0; 0, 0, 1] := by
  rw [inv_eq_of_mul_eq_one_right (gen₂_mul_gen₂_inv v ϖ hπ), coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem coe_conj₂ (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (m : LocalGL3 v) :
    ((((iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v)⁻¹ * m *
        iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1,
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ *
            (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2;
        (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1,
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ *
            (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2;
        (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 *
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 *
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ,
          (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2] := by
  rw [Units.val_mul, Units.val_mul, coe_gen₂, coe_gen₂_inv]
  have hπ' := coe_integers_ne_zero v hπ
  have key : ∀ x : v.adicCompletion ℚ, (ϖ : v.adicCompletion ℚ)⁻¹ * x * ϖ = x := fun x => by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ', one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, key, hπ']

private theorem conj₂_mem_congrSubgroup (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} (hc : 1 ≤ c) {m : LocalGL3 v} (hm : m ∈ congrSubgroup v c)
    (h02 : Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2) ≤ WithZero.exp (-(c : ℤ) - 1))
    (h12 : Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2) ≤ WithZero.exp (-(c : ℤ) - 1)) :
    (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v)⁻¹ * m *
      iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ∈ congrSubgroup v c := by
  have hmi : m⁻¹ ∈ congrSubgroup v c := inv_mem hm
  have hϖ1 : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≤ 1 := by
    rw [hϖ, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hϖinv : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ = WithZero.exp (1 : ℤ) := by
    rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]
  have hdeep : ∀ {x : v.adicCompletion ℚ}, Valued.v x ≤ WithZero.exp (-(c : ℤ) - 1) →
      Valued.v ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ * x) ≤ WithZero.exp (-(c : ℤ)) := by
    intro x hx
    rw [Valuation.map_mul, hϖinv]
    calc WithZero.exp (1 : ℤ) * Valued.v x ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-(c : ℤ) - 1) :=
          mul_le_mul_right hx _
      _ = WithZero.exp (-(c : ℤ)) := by rw [← WithZero.exp_add]; congr 1; ring
  have hint : ∀ {x : v.adicCompletion ℚ}, Valued.v x ≤ WithZero.exp (-(c : ℤ)) →
      Valued.v ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)⁻¹ * x) ≤ 1 := by
    intro x hx
    rw [Valuation.map_mul, hϖinv]
    calc WithZero.exp (1 : ℤ) * Valued.v x ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-(c : ℤ)) := mul_le_mul_right hx _
      _ = WithZero.exp (1 - (c : ℤ)) := by rw [← WithZero.exp_add, sub_eq_add_neg]
      _ ≤ 1 := by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)
  have hright : ∀ {x : v.adicCompletion ℚ} {ε : ℤᵐ⁰}, Valued.v x ≤ ε →
      Valued.v (x * algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≤ ε :=
    fun hx => valued_mul_le_right v hx hϖ1
  have hconj_inv : ((iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) :
      LocalGL3 v)⁻¹ * m * iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ))⁻¹ =
      (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v)⁻¹ * m⁻¹ *
        iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) := by
    group
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [coe_conj₂]
    fin_cases i <;> fin_cases j
    · simpa using valued_entry_le v hm 0 0
    · simpa using valued_entry_le v hm 0 1
    · simpa using hint (le_trans h02 (exp_deeper_le c))
    · simpa using valued_entry_le v hm 1 0
    · simpa using valued_entry_le v hm 1 1
    · simpa using hint (le_trans h12 (exp_deeper_le c))
    · simpa using hright (valued_entry_le v hm 2 0)
    · simpa using hright (valued_entry_le v hm 2 1)
    · simpa using valued_entry_le v hm 2 2
  · rw [hconj_inv, coe_conj₂]
    fin_cases i <;> fin_cases j
    · simpa using valued_entry_le v hmi 0 0
    · simpa using valued_entry_le v hmi 0 1
    · simpa using hint (valued_off_le v hmi (by decide : (0 : Fin 3) ≠ 2))
    · simpa using valued_entry_le v hmi 1 0
    · simpa using valued_entry_le v hmi 1 1
    · simpa using hint (valued_off_le v hmi (by decide : (1 : Fin 3) ≠ 2))
    · simpa using hright (valued_entry_le v hmi 2 0)
    · simpa using hright (valued_entry_le v hmi 2 1)
    · simpa using valued_entry_le v hmi 2 2
  · rw [coe_conj₂]
    fin_cases i <;> fin_cases j
    · simpa using valued_diag_le v hm 0
    · simpa using valued_off_le v hm (by decide : (0 : Fin 3) ≠ 1)
    · simpa using hdeep h02
    · simpa using valued_off_le v hm (by decide : (1 : Fin 3) ≠ 0)
    · simpa using valued_diag_le v hm 1
    · simpa using hdeep h12
    · simpa using hright (valued_off_le v hm (by decide : (2 : Fin 3) ≠ 0))
    · simpa using hright (valued_off_le v hm (by decide : (2 : Fin 3) ≠ 1))
    · simpa using valued_diag_le v hm 2

private noncomputable def shift₂ (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} {k : LocalGL3 v} (hk : k ∈ congrSubgroup v c) : Res v × Res v :=
  (resOf v _ (valued_quot_le_one v hϖ (valued_off_le v hk (by decide : (1 : Fin 3) ≠ 2))),
    resOf v _ (valued_quot_le_one v hϖ (valued_off_le v hk (by decide : (0 : Fin 3) ≠ 2))))

private theorem translate₂ (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} (hc : 1 ≤ c) {k : LocalGL3 v} (hk : k ∈ congrSubgroup v c) (i : Res v × Res v) :
    let m : LocalGL3 v := (upperUnipotent3 0 (rep v ϖ c (i + shift₂ v hϖ hk).1) (rep v ϖ c (i + shift₂ v hϖ hk).2) :
      LocalGL3 v)⁻¹ * k * upperUnipotent3 0 (rep v ϖ c i.1) (rep v ϖ c i.2)
    m ∈ congrSubgroup v c ∧
      Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2) ≤ WithZero.exp (-(c : ℤ) - 1) ∧
      Valued.v ((m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2) ≤ WithZero.exp (-(c : ℤ) - 1) := by
  intro m
  have hy := valued_rep_le v hϖ c i.1
  have hz := valued_rep_le v hϖ c i.2
  have hy' := valued_rep_le v hϖ c (i + shift₂ v hϖ hk).1
  have hz' := valued_rep_le v hϖ c (i + shift₂ v hϖ hk).2
  have hy1 := valued_le_one_of_le_exp_neg v hy
  have hzero : Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp (-(c : ℤ)) := by simp
  refine ⟨mul_mem (mul_mem (inv_mem (upperUnipotent3_mem_congrSubgroup v hzero hy' hz')) hk)
    (upperUnipotent3_mem_congrSubgroup v hzero hy hz), ?_, ?_⟩
  ·
    have hid : (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 =
        ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 - 1) * rep v ϖ c i.2 +
          (rep v ϖ c i.2 + (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 -
            rep v ϖ c (i + shift₂ v hϖ hk).2) +
          (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 * rep v ϖ c i.1 +
          (-(rep v ϖ c (i + shift₂ v hϖ hk).2 *
            ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 * rep v ϖ c i.2 +
              (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 * rep v ϖ c i.1))) +
          (-(rep v ϖ c (i + shift₂ v hϖ hk).2 * ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 - 1))) := by
      simp only [m, Units.val_mul, coe_upperUnipotent3_inv, upperUnipotent3_coe, Matrix.mul_apply,
        Fin.sum_univ_three]
      simp
      ring
    have hshift : (i + shift₂ v hϖ hk).2 = i.2 + resOf v _ (valued_quot_le_one v hϖ
        (valued_off_le v hk (by decide : (0 : Fin 3) ≠ 2))) := rfl
    rw [hid]
    refine valued_add_le v (valued_add_le v (valued_add_le v (valued_add_le v ?_ ?_) ?_) ?_) ?_
    · exact valued_mul_le_deeper v hc (valued_diag_le v hk 0) hz
    · rw [hshift]
      exact valued_rep_add_sub_rep_add v hπ hϖ c i.2 (valued_off_le v hk (by decide))
    · exact valued_mul_le_deeper v hc (valued_off_le v hk (by decide)) hy
    · exact valued_neg_le v (valued_mul_le_deeper v hc hz'
        (valued_add_le v (valued_mul_le_left v (valued_entry_le v hk 2 0) hz)
          (valued_mul_le_right v (valued_off_le v hk (by decide)) hy1)))
    · exact valued_neg_le v (valued_mul_le_deeper v hc hz' (valued_diag_le v hk 2))
  ·
    have hid : (m : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 =
        (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * rep v ϖ c i.2 +
          ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 - 1) * rep v ϖ c i.1 +
          (rep v ϖ c i.1 + (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 -
            rep v ϖ c (i + shift₂ v hϖ hk).1) +
          (-(rep v ϖ c (i + shift₂ v hϖ hk).1 *
            ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 * rep v ϖ c i.2 +
              (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 * rep v ϖ c i.1))) +
          (-(rep v ϖ c (i + shift₂ v hϖ hk).1 * ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 - 1))) := by
      simp only [m, Units.val_mul, coe_upperUnipotent3_inv, upperUnipotent3_coe, Matrix.mul_apply,
        Fin.sum_univ_three]
      simp
      ring
    have hshift : (i + shift₂ v hϖ hk).1 = i.1 + resOf v _ (valued_quot_le_one v hϖ
        (valued_off_le v hk (by decide : (1 : Fin 3) ≠ 2))) := rfl
    rw [hid]
    refine valued_add_le v (valued_add_le v (valued_add_le v (valued_add_le v ?_ ?_) ?_) ?_) ?_
    · exact valued_mul_le_deeper v hc (valued_off_le v hk (by decide)) hz
    · exact valued_mul_le_deeper v hc (valued_diag_le v hk 1) hy
    · rw [hshift]
      exact valued_rep_add_sub_rep_add v hπ hϖ c i.1 (valued_off_le v hk (by decide))
    · exact valued_neg_le v (valued_mul_le_deeper v hc hy'
        (valued_add_le v (valued_mul_le_left v (valued_entry_le v hk 2 0) hz)
          (valued_mul_le_right v (valued_off_le v hk (by decide)) hy1)))
    · exact valued_neg_le v (valued_mul_le_deeper v hc hy' (valued_diag_le v hk 2))

end SecondOperator

section Operators

private noncomputable def hecke₁ (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (c : ℕ) :
    (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun G := fun g => ∑ i : Res v × Res v,
    G (g * (upperUnipotent3 (rep v ϖ c i.1) 0 (rep v ϖ c i.2) *
      iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1)))
  map_add' G₁ G₂ := by
    funext g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a G := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

private noncomputable def hecke₂ (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (c : ℕ) :
    (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun G := fun g => ∑ i : Res v × Res v,
    G (g * (upperUnipotent3 0 (rep v ϖ c i.1) (rep v ϖ c i.2) *
      iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)))
  map_add' G₁ G₂ := by
    funext g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a G := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

private theorem hecke₁_apply (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (c : ℕ) (G : LocalGL3 v → ℂ)
    (g : LocalGL3 v) :
    hecke₁ v ϖ hπ c G g = ∑ i : Res v × Res v,
      G (g * (upperUnipotent3 (rep v ϖ c i.1) 0 (rep v ϖ c i.2) *
        iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1))) := rfl

private theorem hecke₂_apply (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (c : ℕ) (G : LocalGL3 v → ℂ)
    (g : LocalGL3 v) :
    hecke₂ v ϖ hπ c G g = ∑ i : Res v × Res v,
      G (g * (upperUnipotent3 0 (rep v ϖ c i.1) (rep v ϖ c i.2) *
        iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ))) := rfl

private theorem hecke₁_mem (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (c : ℕ) (W : LocalGL3 v → ℂ)
    {G : LocalGL3 v → ℂ} (hG : G ∈ gl3CyclicSubspace W) : hecke₁ v ϖ hπ c G ∈ gl3CyclicSubspace W := by
  have hfun : hecke₁ v ϖ hπ c G = ∑ i : Res v × Res v,
      gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 (rep v ϖ c i.1) 0 (rep v ϖ c i.2) *
        iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1)) G := by
    funext g
    simp only [hecke₁_apply, Finset.sum_apply, gl3AmbientRightTranslate_apply]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hG

private theorem hecke₂_mem (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (c : ℕ) (W : LocalGL3 v → ℂ)
    {G : LocalGL3 v → ℂ} (hG : G ∈ gl3CyclicSubspace W) : hecke₂ v ϖ hπ c G ∈ gl3CyclicSubspace W := by
  have hfun : hecke₂ v ϖ hπ c G = ∑ i : Res v × Res v,
      gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 (rep v ϖ c i.1) (rep v ϖ c i.2) *
        iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) G := by
    funext g
    simp only [hecke₂_apply, Finset.sum_apply, gl3AmbientRightTranslate_apply]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hG

private theorem hecke₁_invariant (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} (hc : 1 ≤ c) {G : LocalGL3 v → ℂ}
    (hG : ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, G (g * k) = G g) :
    ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, hecke₁ v ϖ hπ c G (g * k) = hecke₁ v ϖ hπ c G g := by
  intro k hk g
  rw [hecke₁_apply, hecke₁_apply]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight (shift₁ v hϖ hk))]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hm, h01, h02⟩ := translate₁ v hπ hϖ hc hk i
  have hκ := conj₁_mem_congrSubgroup v hπ hϖ hc hm h01 h02
  have hid : g * k * (upperUnipotent3 (rep v ϖ c i.1) 0 (rep v ϖ c i.2) *
      iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1)) =
      g * (upperUnipotent3 (rep v ϖ c (Equiv.addRight (shift₁ v hϖ hk) i).1) 0
          (rep v ϖ c (Equiv.addRight (shift₁ v hϖ hk) i).2) *
        iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1)) *
      ((iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1) : LocalGL3 v)⁻¹ *
        ((upperUnipotent3 (rep v ϖ c (i + shift₁ v hϖ hk).1) 0 (rep v ϖ c (i + shift₁ v hϖ hk).2) :
          LocalGL3 v)⁻¹ * k * upperUnipotent3 (rep v ϖ c i.1) 0 (rep v ϖ c i.2)) *
        iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1)) := by
    simp only [Equiv.coe_addRight]
    group
  rw [hid, hG _ hκ]

private theorem hecke₂_invariant (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {c : ℕ} (hc : 1 ≤ c) {G : LocalGL3 v → ℂ}
    (hG : ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, G (g * k) = G g) :
    ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, hecke₂ v ϖ hπ c G (g * k) = hecke₂ v ϖ hπ c G g := by
  intro k hk g
  rw [hecke₂_apply, hecke₂_apply]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight (shift₂ v hϖ hk))]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hm, h02, h12⟩ := translate₂ v hπ hϖ hc hk i
  have hκ := conj₂_mem_congrSubgroup v hπ hϖ hc hm h02 h12
  have hid : g * k * (upperUnipotent3 0 (rep v ϖ c i.1) (rep v ϖ c i.2) *
      iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) =
      g * (upperUnipotent3 0 (rep v ϖ c (Equiv.addRight (shift₂ v hϖ hk) i).1)
          (rep v ϖ c (Equiv.addRight (shift₂ v hϖ hk) i).2) *
        iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) *
      ((iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : LocalGL3 v)⁻¹ *
        ((upperUnipotent3 0 (rep v ϖ c (i + shift₂ v hϖ hk).1) (rep v ϖ c (i + shift₂ v hϖ hk).2) :
          LocalGL3 v)⁻¹ * k * upperUnipotent3 0 (rep v ϖ c i.1) (rep v ϖ c i.2)) *
        iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) := by
    simp only [Equiv.coe_addRight]
    group
  rw [hid, hG _ hκ]

private theorem card_res_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : ((Fintype.card (Res v) : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

end Operators

section WhittakerLaw

variable {F : Type*} [CommRing F] {R : Type*} [CommRing R]

private theorem whittaker_apply_unipotent_mul {ψ : AddChar F R} {W : GL (Fin 3) F → R} (hW : IsGL3PsiWhittakerFn ψ W)
    {G : GL (Fin 3) F → R} (hG : G ∈ gl3CyclicSubspace W) (x y z : F) (g : GL (Fin 3) F) :
    G (upperUnipotent3 x y z * g) = ψ (x + y) * G g := by
  refine Submodule.span_induction (p := fun f _ => f (upperUnipotent3 x y z * g) = ψ (x + y) * f g) ?_ ?_ ?_ ?_ hG
  · rintro _ ⟨h, rfl⟩
    simp only [gl3AmbientRightTranslate_apply, mul_assoc]
    exact hW x y z (g * h)
  · simp
  · intro f₁ f₂ _ _ h₁ h₂
    simp only [Pi.add_apply, h₁, h₂, mul_add]
  · intro r f _ h
    simp only [Pi.smul_apply, smul_eq_mul, h, mul_left_comm]

end WhittakerLaw

section Torus

variable {K : Type*} [Field K]

private def tor (π : K) (hπ : π ≠ 0) (k m : ℤ) : GL (Fin 3) K :=
  iotaGL (diagZ π hπ k * scalarPi π hπ ^ m)

private theorem coe_scalarPi_zpow (π : K) (hπ : π ≠ 0) (m : ℤ) :
    ((scalarPi π hπ ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (π ^ m) := by
  have h : scalarPi π hπ = Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom
      (Units.mk0 π hπ) := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarPi, Matrix.scalar_apply]
  rw [h, ← map_zpow, Units.coe_map]
  simp [Units.val_zpow_eq_zpow_val]

private theorem coe_tor (π : K) (hπ : π ≠ 0) (k m : ℤ) :
    ((tor π hπ k m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![π ^ k * π ^ m, π ^ m, 1] := by
  unfold tor
  rw [coe_iotaGL, Units.val_mul, coe_scalarPi_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagZ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem tor_mul_unipotent (π : K) (hπ : π ≠ 0) (k m : ℤ) (x y z : K) :
    tor π hπ k m * upperUnipotent3 x y z =
      upperUnipotent3 (π ^ k * x) (π ^ m * y) (π ^ k * π ^ m * z) * tor π hπ k m := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_tor]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

private theorem tor_mul_gen₁ (π : K) (hπ : π ≠ 0) (k m : ℤ) :
    tor π hπ k m * iotaGL (diagZ π hπ 1) = tor π hπ (k + 1) m := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_tor, coe_tor, coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagZ, zpow_add_one₀ hπ]
  ring

private theorem tor_mul_gen₂ (π : K) (hπ : π ≠ 0) (k m : ℤ) :
    tor π hπ k m * iotaGL (scalarPi π hπ) = tor π hπ k (m + 1) := by
  unfold tor
  rw [← map_mul, mul_assoc, ← zpow_add_one]

end Torus

section ValuationEstimate

private theorem valued_zpow_mul_le (v : HeightOneSpectrum (𝓞 ℚ)) {π : v.adicCompletion ℚ}
    (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (k : ℤ) {r : v.adicCompletion ℚ} {c : ℤ}
    (hr : Valued.v r ≤ WithZero.exp (-c)) : Valued.v (π ^ k * r) ≤ WithZero.exp (-(k + c)) := by
  have hk : Valued.v (π ^ k) = WithZero.exp (-k) := by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
    congr 1
    simp
  rw [map_mul, hk, neg_add, WithZero.exp_add]
  exact mul_le_mul_right hr _

end ValuationEstimate

section Recursion

private def HasRec (a : ℤ → ℂ) (t : ℤ) {d : ℕ} (cs : Fin d → ℂ) : Prop :=
  ∀ k : ℤ, t ≤ k → a (k + (d : ℤ)) = ∑ i : Fin d, cs i * a (k + ((i : ℕ) : ℤ))

private theorem hasRec_mono {a : ℤ → ℂ} {t t' : ℤ} (htt' : t ≤ t') {d : ℕ} {cs : Fin d → ℂ}
    (h : HasRec a t cs) : HasRec a t' cs :=
  fun k hk => h k (le_trans htt' hk)

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem ev_pow_apply (T : Module.End ℂ M) (c : ℂ) (ev : ℤ → M →ₗ[ℂ] ℂ) (t : ℤ)
    (hT : ∀ (u : M) (k : ℤ), t ≤ k → ev k (T u) = c * ev (k + 1) u) (n : ℕ) (u : M) (k : ℤ) (hk : t ≤ k) :
    ev k ((T ^ n) u) = c ^ n * ev (k + (n : ℤ)) u := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, hT _ k hk, ih (k + 1) (by omega)]
    have e : k + 1 + (n : ℤ) = k + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    ring

variable [FiniteDimensional ℂ M]

private noncomputable def recDeg (T : Module.End ℂ M) : ℕ := (LinearMap.charpoly T).natDegree

private noncomputable def recCoeff (T : Module.End ℂ M) (c : ℂ) (i : Fin (recDeg T)) : ℂ :=
  -((LinearMap.charpoly T).coeff (i : ℕ) * c ^ (i : ℕ)) / c ^ recDeg T

private theorem hasRec_of_ev (T : Module.End ℂ M) {c : ℂ} (hc : c ≠ 0) (ev : ℤ → M →ₗ[ℂ] ℂ) (t : ℤ)
    (hT : ∀ (u : M) (k : ℤ), t ≤ k → ev k (T u) = c * ev (k + 1) u) (u : M) :
    HasRec (fun k => ev k u) t (recCoeff T c) := by
  unfold HasRec
  intro k hk
  dsimp only
  have h0 : ∑ i ∈ Finset.range ((LinearMap.charpoly T).natDegree + 1),
      (LinearMap.charpoly T).coeff i * ev k ((T ^ i) u) = 0 := by
    have h := LinearMap.aeval_self_charpoly T
    rw [Polynomial.aeval_eq_sum_range] at h
    have h' := congrArg (fun f : Module.End ℂ M => ev k (f u)) h
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, map_sum, map_smul,
      smul_eq_mul, map_zero] using h'
  have h1 : ∑ i ∈ Finset.range (recDeg T + 1),
      (LinearMap.charpoly T).coeff i * (c ^ i * ev (k + (i : ℤ)) u) = 0 := by
    calc ∑ i ∈ Finset.range (recDeg T + 1), (LinearMap.charpoly T).coeff i * (c ^ i * ev (k + (i : ℤ)) u)
        = ∑ i ∈ Finset.range (recDeg T + 1), (LinearMap.charpoly T).coeff i * ev k ((T ^ i) u) :=
          Finset.sum_congr rfl fun i _ => by rw [ev_pow_apply T c ev t hT i u k hk]
      _ = 0 := h0
  rw [Finset.sum_range_succ] at h1
  have hmon : (LinearMap.charpoly T).coeff (recDeg T) = 1 := (LinearMap.charpoly_monic T).coeff_natDegree
  rw [hmon, one_mul] at h1
  have hcd : c ^ recDeg T ≠ 0 := pow_ne_zero _ hc
  have hF : ∑ i : Fin (recDeg T), recCoeff T c i * ev (k + ((i : ℕ) : ℤ)) u =
      ∑ j ∈ Finset.range (recDeg T),
        -((LinearMap.charpoly T).coeff j * c ^ j) / c ^ recDeg T * ev (k + (j : ℤ)) u :=
    Fin.sum_univ_eq_sum_range
      (fun j => -((LinearMap.charpoly T).coeff j * c ^ j) / c ^ recDeg T * ev (k + (j : ℤ)) u) (recDeg T)
  have hS : ∑ j ∈ Finset.range (recDeg T),
      -((LinearMap.charpoly T).coeff j * c ^ j) / c ^ recDeg T * ev (k + (j : ℤ)) u =
      (-(∑ j ∈ Finset.range (recDeg T), (LinearMap.charpoly T).coeff j * (c ^ j * ev (k + (j : ℤ)) u))) /
        c ^ recDeg T := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hF, hS, eq_div_iff hcd]
  linear_combination h1

end Recursion

section Padding

private def padList {d : ℕ} (cs : Fin d → ℂ) : Fin (d + 1) → ℂ := Fin.cons (0 : ℂ) cs

private theorem hasRec_padList {a : ℤ → ℂ} {t : ℤ} {d : ℕ} {cs : Fin d → ℂ} (h : HasRec a t cs) :
    HasRec a (t - 1) (padList cs) := by
  intro k hk
  have h1 := h (k + 1) (by omega)
  have e : k + ((d + 1 : ℕ) : ℤ) = k + 1 + (d : ℤ) := by push_cast; ring
  rw [e, h1, Fin.sum_univ_succ]
  simp only [padList, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [Fin.val_succ]
  push_cast
  ring

private def padN {d : ℕ} : (n : ℕ) → (Fin d → ℂ) → Fin (d + n) → ℂ
  | 0, cs => cs
  | n + 1, cs => padList (padN n cs)

private theorem hasRec_padN {a : ℤ → ℂ} {t : ℤ} {d : ℕ} {cs : Fin d → ℂ} (h : HasRec a t cs) (n : ℕ) :
    HasRec a (t - (n : ℤ)) (padN n cs) := by
  induction n with
  | zero => simpa [padN] using h
  | succ n ih =>
    have e : t - ((n + 1 : ℕ) : ℤ) = t - (n : ℤ) - 1 := by push_cast; ring
    rw [e]
    exact hasRec_padList ih

end Padding

section Growth

private theorem norm_le_of_hasRec {e : ℤ → ℂ} {t : ℤ} {d : ℕ} {cs : Fin d → ℂ} (h : HasRec e t cs)
    {B R : ℝ} (hB : 0 ≤ B) (hR1 : 1 ≤ R) (hRS : ∑ i : Fin d, ‖cs i‖ ≤ R)
    (hbase : ∀ i : ℕ, i < d → ‖e (t + (i : ℤ))‖ ≤ B) (i : ℕ) : ‖e (t + (i : ℤ))‖ ≤ B * R ^ i := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hzero : ∀ j : ℕ, e (t + (j : ℤ)) = 0 := fun j => by
      have := h (t + (j : ℤ)) (by omega)
      simpa using this
    rw [hzero]
    simp only [norm_zero]
    positivity
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  suffices H : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → ‖e (t + (j : ℤ))‖ ≤ B * R ^ j from H i i le_rfl
  intro n
  induction n with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using hbase 0 (by omega)
  | succ n ih =>
    intro j hj
    rcases lt_or_ge j (d' + 1) with hjd | hjd
    · calc ‖e (t + (j : ℤ))‖ ≤ B := hbase j hjd
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * R ^ j := by gcongr; exact one_le_pow₀ hR1
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + (d' + 1) := ⟨j - (d' + 1), by omega⟩
      have hrec := h (t + (j' : ℤ)) (by omega)
      have e1 : t + ((j' + (d' + 1) : ℕ) : ℤ) = t + (j' : ℤ) + ((d' + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, hrec]
      have hterm : ∀ l : Fin (d' + 1),
          ‖cs l * e (t + (j' : ℤ) + ((l : ℕ) : ℤ))‖ ≤ ‖cs l‖ * (B * R ^ (j' + d')) := by
        intro l
        rw [norm_mul]
        have hl : (l : ℕ) ≤ d' := Nat.lt_succ_iff.mp l.is_lt
        have e2 : t + (j' : ℤ) + ((l : ℕ) : ℤ) = t + ((j' + (l : ℕ) : ℕ) : ℤ) := by push_cast; ring
        rw [e2]
        have hih := ih (j' + (l : ℕ)) (by omega)
        calc ‖cs l‖ * ‖e (t + ((j' + (l : ℕ) : ℕ) : ℤ))‖ ≤ ‖cs l‖ * (B * R ^ (j' + (l : ℕ))) := by
              gcongr
          _ ≤ ‖cs l‖ * (B * R ^ (j' + d')) := by gcongr
      calc ‖∑ l : Fin (d' + 1), cs l * e (t + (j' : ℤ) + ((l : ℕ) : ℤ))‖
          ≤ ∑ l : Fin (d' + 1), ‖cs l * e (t + (j' : ℤ) + ((l : ℕ) : ℤ))‖ := norm_sum_le _ _
        _ ≤ ∑ l : Fin (d' + 1), ‖cs l‖ * (B * R ^ (j' + d')) := Finset.sum_le_sum fun l _ => hterm l
        _ = (∑ l : Fin (d' + 1), ‖cs l‖) * (B * R ^ (j' + d')) := by rw [Finset.sum_mul]
        _ ≤ R * (B * R ^ (j' + d')) := by gcongr
        _ = B * R ^ (j' + (d' + 1)) := by ring

private theorem exists_bound_of_hasRec {a : ℤ → ℤ → ℂ} (L : ℕ) {d₁ d₂ : ℕ} {c₁ : Fin d₁ → ℂ} {c₂ : Fin d₂ → ℂ}
    (h₁ : ∀ m : ℤ, -(L : ℤ) ≤ m → HasRec (fun k => a k m) (-(L : ℤ)) c₁)
    (h₂ : ∀ k : ℤ, -(L : ℤ) ≤ k → HasRec (fun m => a k m) (-(L : ℤ)) c₂) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
      ‖a k m‖ ≤ C * R ^ ((k + L).toNat + (m + L).toNat) := by
  set C : ℝ := ∑ i : Fin d₁, ∑ j : Fin d₂, ‖a (-(L : ℤ) + ((i : ℕ) : ℤ)) (-(L : ℤ) + ((j : ℕ) : ℤ))‖ with hC
  set R : ℝ := max 1 (max (∑ i : Fin d₁, ‖c₁ i‖) (∑ i : Fin d₂, ‖c₂ i‖)) with hRdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  have hRS₁ : ∑ i : Fin d₁, ‖c₁ i‖ ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRS₂ : ∑ i : Fin d₂, ‖c₂ i‖ ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)

  have hblock : ∀ i j : ℕ, i < d₁ → j < d₂ → ‖a (-(L : ℤ) + (i : ℤ)) (-(L : ℤ) + (j : ℤ))‖ ≤ C := by
    intro i j hi hj
    calc ‖a (-(L : ℤ) + (i : ℤ)) (-(L : ℤ) + (j : ℤ))‖
        ≤ ∑ j' : Fin d₂, ‖a (-(L : ℤ) + (((⟨i, hi⟩ : Fin d₁) : ℕ) : ℤ)) (-(L : ℤ) + ((j' : ℕ) : ℤ))‖ :=
          Finset.single_le_sum (f := fun j' : Fin d₂ =>
            ‖a (-(L : ℤ) + (((⟨i, hi⟩ : Fin d₁) : ℕ) : ℤ)) (-(L : ℤ) + ((j' : ℕ) : ℤ))‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ (⟨j, hj⟩ : Fin d₂))
      _ ≤ C := Finset.single_le_sum (f := fun i' : Fin d₁ =>
            ∑ j' : Fin d₂, ‖a (-(L : ℤ) + ((i' : ℕ) : ℤ)) (-(L : ℤ) + ((j' : ℕ) : ℤ))‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (⟨i, hi⟩ : Fin d₁))

  have hrows : ∀ j : ℕ, j < d₂ → ∀ i : ℕ, ‖a (-(L : ℤ) + (i : ℤ)) (-(L : ℤ) + (j : ℤ))‖ ≤ C * R ^ i := by
    intro j hj i
    exact norm_le_of_hasRec (h₁ (-(L : ℤ) + (j : ℤ)) (by omega)) hC0 hR1 hRS₁
      (fun i' hi' => hblock i' j hi' hj) i

  have hall : ∀ i j : ℕ, ‖a (-(L : ℤ) + (i : ℤ)) (-(L : ℤ) + (j : ℤ))‖ ≤ C * R ^ (i + j) := by
    intro i j
    have hcol := norm_le_of_hasRec (h₂ (-(L : ℤ) + (i : ℤ)) (by omega)) (B := C * R ^ i)
      (by positivity) hR1 hRS₂ (fun j' hj' => hrows j' hj' i) j
    calc ‖a (-(L : ℤ) + (i : ℤ)) (-(L : ℤ) + (j : ℤ))‖ ≤ C * R ^ i * R ^ j := hcol
      _ = C * R ^ (i + j) := by rw [pow_add, mul_assoc]
  refine ⟨C, R, hC0, hR1, fun k m hk hm => ?_⟩
  have ek : k = -(L : ℤ) + (((k + L).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have em : m = -(L : ℤ) + (((m + L).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  calc ‖a k m‖ = ‖a (-(L : ℤ) + (((k + L).toNat : ℕ) : ℤ)) (-(L : ℤ) + (((m + L).toNat : ℕ) : ℤ))‖ := by
        rw [← ek, ← em]
    _ ≤ C * R ^ ((k + L).toNat + (m + L).toNat) := hall _ _

end Growth

section Support

private theorem valued_unipotent_entry_le (v : HeightOneSpectrum (𝓞 ℚ)) {x y z : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) (hz : Valued.v z ≤ 1) (i j : Fin 3) :
    Valued.v (((upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [hx, hy, hz]

private theorem unipotent_inv (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) :=
  Units.ext rfl

private theorem unipotent_mem_congrSubgroup (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) {x y z : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) (hy : Valued.v y ≤ WithZero.exp (-(c : ℤ)))
    (hz : Valued.v z ≤ WithZero.exp (-(c : ℤ))) : (upperUnipotent3 x y z : LocalGL3 v) ∈ congrSubgroup v c := by
  have h1 : WithZero.exp (-(c : ℤ)) ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
  rw [WithZero.exp_zero] at h1
  have hx1 : Valued.v x ≤ 1 := le_trans hx h1
  have hy1 : Valued.v y ≤ 1 := le_trans hy h1
  have hz1 : Valued.v z ≤ 1 := le_trans hz h1
  rw [mem_congrSubgroup_iff]
  refine ⟨⟨valued_unipotent_entry_le v hx1 hy1 hz1, ?_⟩, ?_⟩
  · rw [unipotent_inv]
    refine valued_unipotent_entry_le v ?_ ?_ ?_
    · rwa [Valuation.map_neg]
    · rwa [Valuation.map_neg]
    · refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ hz1)
      rw [Valuation.map_mul]
      exact mul_le_one' hx1 hy1
  · intro i j
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hx | simpa using hy | simpa using hz

private theorem eq_zero_of_fst (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {η : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn η W) (c : ℕ)
    {F : LocalGL3 v → ℂ} (hF : F ∈ gl3CyclicSubspace W)
    (hinv : ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, F (g * k) = F g) (k m : ℤ)
    {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ WithZero.exp (-(k + (c : ℤ)))) (hy1 : η y ≠ 1) :
    F (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) = 0 := by
  have hy' : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ (-k) * y) ≤
      WithZero.exp (-(c : ℤ)) := by
    have h := valued_zpow_mul_le v hϖ (-k) hy
    rwa [show -(-k + (k + (c : ℤ))) = -(c : ℤ) by ring] at h
  have hu := unipotent_mem_congrSubgroup v c (y := 0) (z := 0) hy' (by simp) (by simp)
  have h1 := hinv _ hu (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m)
  rw [tor_mul_unipotent, whittaker_apply_unipotent_mul hW hF, mul_zero, add_zero, ← mul_assoc,
    ← zpow_add₀ hπ, add_neg_cancel, zpow_zero, one_mul] at h1
  have h2 : (η y - 1) * F (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hy1)

private theorem eq_zero_of_snd (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {η : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn η W) (c : ℕ)
    {F : LocalGL3 v → ℂ} (hF : F ∈ gl3CyclicSubspace W)
    (hinv : ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, F (g * k) = F g) (k m : ℤ)
    {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ WithZero.exp (-(m + (c : ℤ)))) (hy1 : η y ≠ 1) :
    F (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) = 0 := by
  have hy' : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ (-m) * y) ≤
      WithZero.exp (-(c : ℤ)) := by
    have h := valued_zpow_mul_le v hϖ (-m) hy
    rwa [show -(-m + (m + (c : ℤ))) = -(c : ℤ) by ring] at h
  have hu := unipotent_mem_congrSubgroup v c (x := 0) (z := 0) (by simp) hy' (by simp)
  have h1 := hinv _ hu (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m)
  rw [tor_mul_unipotent, whittaker_apply_unipotent_mul hW hF, mul_zero, zero_add, ← mul_assoc,
    ← zpow_add₀ hπ, add_neg_cancel, zpow_zero, one_mul] at h1
  have h2 : (η y - 1) * F (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hy1)

private theorem invariant_of_level (v : HeightOneSpectrum (𝓞 ℚ)) {F : LocalGL3 v → ℂ} {L : ℕ}
    (hF : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(L : ℤ))) →
      ∀ g : LocalGL3 v, F (g * k) = F g)
    {c : ℕ} (hLc : L ≤ c) : ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, F (g * k) = F g := by
  intro k hk g
  rw [mem_congrSubgroup_iff] at hk
  exact hF k hk.1 (fun i j => le_trans (hk.2 i j) (WithZero.exp_le_exp.mpr (by omega))) g

end Support

section Cone

private theorem hecke₁_tor (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {η : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn η W) {n₀ : ℕ}
    (hn₀ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(n₀ : ℤ)) → η x = 1) (c : ℕ)
    {G : LocalGL3 v → ℂ} (hG : G ∈ gl3CyclicSubspace W) (k m : ℤ) (hk : (n₀ : ℤ) - c ≤ k) :
    hecke₁ v ϖ hπ c G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) =
      ((Fintype.card (Res v) : ℕ) : ℂ) ^ 2 *
        G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (k + 1) m) := by
  rw [hecke₁_apply]
  have hterm : ∀ i : Res v × Res v,
      G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m *
        (upperUnipotent3 (rep v ϖ c i.1) 0 (rep v ϖ c i.2) *
          iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1))) =
      G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (k + 1) m) := by
    intro i
    rw [← mul_assoc, tor_mul_unipotent, mul_assoc, tor_mul_gen₁, whittaker_apply_unipotent_mul hW hG,
      mul_zero, add_zero, hn₀ _ ?_, one_mul]
    exact le_trans (valued_zpow_mul_le v hϖ k (valued_rep_le v hϖ c i.1))
      (WithZero.exp_le_exp.mpr (by omega))
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    nsmul_eq_mul]
  push_cast
  ring

private theorem hecke₂_tor (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {η : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn η W) {n₀ : ℕ}
    (hn₀ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(n₀ : ℤ)) → η x = 1) (c : ℕ)
    {G : LocalGL3 v → ℂ} (hG : G ∈ gl3CyclicSubspace W) (k m : ℤ) (hm : (n₀ : ℤ) - c ≤ m) :
    hecke₂ v ϖ hπ c G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) =
      ((Fintype.card (Res v) : ℕ) : ℂ) ^ 2 *
        G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k (m + 1)) := by
  rw [hecke₂_apply]
  have hterm : ∀ i : Res v × Res v,
      G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m *
        (upperUnipotent3 0 (rep v ϖ c i.1) (rep v ϖ c i.2) *
          iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ))) =
      G (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k (m + 1)) := by
    intro i
    rw [← mul_assoc, tor_mul_unipotent, mul_assoc, tor_mul_gen₂, whittaker_apply_unipotent_mul hW hG,
      mul_zero, zero_add, hn₀ _ ?_, one_mul]
    exact le_trans (valued_zpow_mul_le v hϖ m (valued_rep_le v hϖ c i.1))
      (WithZero.exp_le_exp.mpr (by omega))
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    nsmul_eq_mul]
  push_cast
  ring

end Cone

section Assembly

private def invSub (v : HeightOneSpectrum (𝓞 ℚ)) (Kc : Subgroup (LocalGL3 v)) : Submodule ℂ (LocalGL3 v → ℂ) where
  carrier := {F | ∀ k ∈ Kc, ∀ g : LocalGL3 v, F (g * k) = F g}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {a b} ha hb k hk g => by
    simp only [Pi.add_apply, ha k hk g, hb k hk g]
  smul_mem' := fun r {a} ha k hk g => by
    simp only [Pi.smul_apply, ha k hk g]

private theorem mem_invSub (v : HeightOneSpectrum (𝓞 ℚ)) (Kc : Subgroup (LocalGL3 v)) (F : LocalGL3 v → ℂ) :
    F ∈ invSub v Kc ↔ ∀ k ∈ Kc, ∀ g : LocalGL3 v, F (g * k) = F g :=
  Iff.rfl

private noncomputable def levelPart (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (c : ℕ) :
    Submodule ℂ (LocalGL3 v → ℂ) :=
  gl3CyclicSubspace W ⊓ invSub v (congrSubgroup v c)

private theorem mem_levelPart (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (c : ℕ)
    (F : LocalGL3 v → ℂ) : F ∈ levelPart v W c ↔
      F ∈ gl3CyclicSubspace W ∧ ∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, F (g * k) = F g :=
  Submodule.mem_inf

private noncomputable def evAt (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (c : ℕ) (g : LocalGL3 v) :
    levelPart v W c →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp (levelPart v W c).subtype

private theorem evAt_apply (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (c : ℕ) (g : LocalGL3 v)
    (u : levelPart v W c) : evAt v W c g u = (u : LocalGL3 v → ℂ) g :=
  rfl

private theorem exists_lists (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    {η : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn η W) {n₀ : ℕ}
    (hn₀ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(n₀ : ℤ)) → η x = 1) (L : ℕ) {c : ℕ}
    (hc1 : 1 ≤ c) (B : Finset (LocalGL3 v → ℂ))
    (hB : ∀ F ∈ gl3CyclicSubspace W, (∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, F (g * k) = F g) →
      F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    ∃ (d₁ : ℕ) (c₁ : Fin d₁ → ℂ) (d₂ : ℕ) (c₂ : Fin d₂ → ℂ), ∀ F ∈ gl3CyclicSubspace W,
      (∀ k ∈ congrSubgroup v c, ∀ g : LocalGL3 v, F (g * k) = F g) →
        (∀ m : ℤ, HasRec
          (fun k => F (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m))
          (-(L : ℤ)) c₁) ∧
        (∀ k : ℤ, HasRec
          (fun m => F (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m))
          (-(L : ℤ)) c₂) := by
  have hUle : levelPart v W c ≤ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := fun F hF =>
    hB F ((mem_levelPart v W c F).mp hF).1 ((mem_levelPart v W c F).mp hF).2
  haveI : FiniteDimensional ℂ (levelPart v W c) := Submodule.finiteDimensional_of_le hUle
  have hT₁ : ∀ F ∈ levelPart v W c, hecke₁ v ϖ hπ c F ∈ levelPart v W c := by
    intro F hF
    rw [mem_levelPart] at hF ⊢
    exact ⟨hecke₁_mem v ϖ hπ c W hF.1, hecke₁_invariant v hπ hϖ hc1 hF.2⟩
  have hT₂ : ∀ F ∈ levelPart v W c, hecke₂ v ϖ hπ c F ∈ levelPart v W c := by
    intro F hF
    rw [mem_levelPart] at hF ⊢
    exact ⟨hecke₂_mem v ϖ hπ c W hF.1, hecke₂_invariant v hπ hϖ hc1 hF.2⟩
  obtain ⟨T₁, hT₁def⟩ : ∃ T : Module.End ℂ (levelPart v W c), T = (hecke₁ v ϖ hπ c).restrict hT₁ := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂def⟩ : ∃ T : Module.End ℂ (levelPart v W c), T = (hecke₂ v ϖ hπ c).restrict hT₂ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ, N = ((Fintype.card (Res v) : ℕ) : ℂ) ^ 2 := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact pow_ne_zero 2 (card_res_ne_zero v)
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (n₀ : ℤ) - c + L ≤ p := ⟨_, Int.self_le_toNat _⟩
  refine ⟨_, padN p (recCoeff T₁ N), _, padN p (recCoeff T₂ N), ?_⟩
  intro F hF hinv
  have hFU : F ∈ levelPart v W c := (mem_levelPart v W c F).mpr ⟨hF, hinv⟩
  constructor
  · intro m
    have h0 : HasRec (fun k => evAt v W c
        (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) ⟨F, hFU⟩)
        ((n₀ : ℤ) - c) (recCoeff T₁ N) := by
      refine hasRec_of_ev T₁ hN0
        (fun k => evAt v W c (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m))
        ((n₀ : ℤ) - c) ?_ ⟨F, hFU⟩
      intro u k hk
      rw [evAt_apply, evAt_apply, hT₁def, LinearMap.coe_restrict_apply, hN]
      exact hecke₁_tor v hπ hϖ hW hn₀ c ((mem_levelPart v W c u).mp u.2).1 k m hk
    exact hasRec_mono (by omega) (hasRec_padN h0 p)
  · intro k
    have h0 : HasRec (fun m => evAt v W c
        (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) ⟨F, hFU⟩)
        ((n₀ : ℤ) - c) (recCoeff T₂ N) := by
      refine hasRec_of_ev T₂ hN0
        (fun m => evAt v W c (tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m))
        ((n₀ : ℤ) - c) ?_ ⟨F, hFU⟩
      intro u m hm
      rw [evAt_apply, evAt_apply, hT₂def, LinearMap.coe_restrict_apply, hN]
      exact hecke₂_tor v hπ hϖ hW hn₀ c ((mem_levelPart v W c u).mp u.2).1 k m hm
    exact hasRec_mono (by omega) (hasRec_padN h0 p)

end Assembly

end TorusRecursion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn.TorusRecursion"

open LanglandsTunnell LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (η : AddChar (v.adicCompletion ℚ) ℂ)
    (hη : ¬ ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → η x = 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (L : ℕ) :
    ∃ (d₁ : ℕ) (c₁ : Fin d₁ → ℂ) (d₂ : ℕ) (c₂ : Fin d₂ → ℂ),
      ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
          (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(L : ℤ))) →
          ∀ g : LocalGL3 v, F (g * k) = F g) →
        (∀ k m : ℤ, k < -(L : ℤ) ∨ m < -(L : ℤ) →
          F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) = 0) ∧
        (∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
          F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (k + d₁) *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) =
            ∑ i : Fin d₁, c₁ i *
              F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (k + (i : ℕ)) *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) ∧
          F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (m + d₂))) =
            ∑ i : Fin d₂, c₂ i *
              F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (m + (i : ℕ))))) ∧
        ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
          ‖F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m))‖ ≤
            C * R ^ ((k + L).toNat + (m + L).toNat) := by
  have _ := hsm
  by_cases hlev : ∃ n₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(n₀ : ℤ)) → η x = 1
  · obtain ⟨n₀, hn₀⟩ := hlev
    obtain ⟨B, hB⟩ := hadm (TorusRecursion.congrSubgroup v (max L 1)) (TorusRecursion.isOpen_congrSubgroup v (max L 1))
    obtain ⟨d₁, c₁, d₂, c₂, hlists⟩ :=
      TorusRecursion.exists_lists v hπ hϖ hW hn₀ L (le_max_right L 1) B hB
    refine ⟨d₁, c₁, d₂, c₂, fun F hF hinvF => ?_⟩
    have hinvL := TorusRecursion.invariant_of_level v hinvF le_rfl
    have hinvL' := TorusRecursion.invariant_of_level v hinvF (le_max_left L 1)
    obtain ⟨hrec₁, hrec₂⟩ := hlists F hF hinvL'
    obtain ⟨y, hy⟩ := not_forall.mp hη
    obtain ⟨hyv, hy1⟩ := Classical.not_imp.mp hy
    refine ⟨fun k m hkm => ?_, fun k m hk hm => ⟨hrec₁ m k hk, hrec₂ k m hm⟩, ?_⟩
    · rcases hkm with hk | hm
      · exact TorusRecursion.eq_zero_of_fst v hπ hϖ hW L hF hinvL k m
          (le_trans hyv (WithZero.exp_le_exp.mpr (by omega))) hy1
      · exact TorusRecursion.eq_zero_of_snd v hπ hϖ hW L hF hinvL k m
          (le_trans hyv (WithZero.exp_le_exp.mpr (by omega))) hy1
    · exact TorusRecursion.exists_bound_of_hasRec L (fun m _ => hrec₁ m) (fun k _ => hrec₂ k)
  · refine ⟨0, fun i => i.elim0, 0, fun i => i.elim0, fun F hF hinvF => ?_⟩
    have hinvL := TorusRecursion.invariant_of_level v hinvF le_rfl
    have hzero : ∀ k m : ℤ,
        F (TorusRecursion.tor (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k m) = 0 := by
      intro k m
      have hnot : ¬ ∀ x : v.adicCompletion ℚ,
          Valued.v x ≤ WithZero.exp (-(((k + L).toNat : ℕ) : ℤ)) → η x = 1 :=
        fun hall => hlev ⟨(k + L).toNat, hall⟩
      obtain ⟨y, hy⟩ := not_forall.mp hnot
      obtain ⟨hyv, hy1⟩ := Classical.not_imp.mp hy
      refine TorusRecursion.eq_zero_of_fst v hπ hϖ hW L hF hinvL k m (le_trans hyv ?_) hy1
      have hself := Int.self_le_toNat (k + (L : ℤ))
      exact WithZero.exp_le_exp.mpr (by omega)
    refine ⟨fun k m _ => hzero k m, fun k m _ _ => ?_, ⟨0, 1, le_rfl, le_rfl, fun k m _ _ => ?_⟩⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, add_zero]
      exact ⟨hzero k m, hzero k m⟩
    · calc _ = ‖(0 : ℂ)‖ := congrArg norm (hzero k m)
        _ ≤ _ := by simp

end S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn (solution)
