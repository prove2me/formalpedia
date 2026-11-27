-- Prove2me | solution 1 for GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:11.017537+00:00
-- url     : https://prove2.me/submissions/0a7f6b51-95c5-456a-9581-d96907d5a7ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EvalTwistTxEqZeroOfAevalArcTx
import Theorems.Thm_GlobalTheory_Ex_NumD_twist_txT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.BddArc
section
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]
end
end GlobalTheory.BddArc
open scoped BigOperators in
private theorem finite_setOf_bilin_self_le_of_posDef {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, B y z = B z y) (hpos : ∀ y, y ≠ 0 → 0 < B y y) (L : ℤ) :
    {y | B y y ≤ L}.Finite := by
  classical
  set b := Module.Free.chooseBasis ℤ X with hb
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℚ :=
    Matrix.of fun i j => (B (b i) (b j) : ℚ)
  let Bq := Matrix.toBilin' M
  let φ : X → Module.Free.ChooseBasisIndex ℤ X → ℚ := fun y i => (b.repr y i : ℚ)
  have hφ : ∀ y z, ((B y z : ℤ) : ℚ) = Bq (φ y) (φ z) := by
    intro y z
    rw [Matrix.toBilin'_apply]
    conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum,
      Int.cast_mul, Finset.mul_sum, M, φ, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hBsymm : LinearMap.IsSymm Bq := by
    refine LinearMap.isSymm_iff_eq_flip.2 (LinearMap.ext₂ fun x y => ?_)
    rw [LinearMap.flip_apply, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [M, Matrix.of_apply, hsymm (b i) (b j)]
    ring
  have hqpos : ∀ v, v ≠ 0 → 0 < Bq v v := by
    intro v hv
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ v
    choose n hn using fun i => hd i (Finset.mem_univ i)
    have hd0 : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    set y : X := b.equivFun.symm n
    have hy : φ y = ((d : ℤ) : ℚ) • v := by
      funext i
      have := hn i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at this
      have hr : b.repr y i = n i := by rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp only [φ, Pi.smul_apply, smul_eq_mul, hr]
      exact this
    have hy0 : y ≠ 0 := by
      intro h
      apply hv
      have h2 : ((d : ℤ) : ℚ) • v = 0 := by rw [← hy, h]; funext i; simp [φ]
      exact (smul_eq_zero.1 h2).resolve_left hd0
    have h1 := hpos y hy0
    have h2 : (0 : ℚ) < Bq (φ y) (φ y) := by rw [← hφ]; exact_mod_cast h1
    rw [hy] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    have h3 : 0 < ((d : ℤ) : ℚ) * ((d : ℤ) : ℚ) := mul_self_pos.2 hd0
    nlinarith
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hw⟩ := LinearMap.BilinForm.exists_orthogonal_basis hBsymm
  have hexp : ∀ v, Bq v v = ∑ k, (w.repr v k) ^ 2 * Bq (w k) (w k) := by
    intro v
    conv_lhs => rw [← w.sum_repr v]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hlk
      rw [hw hlk]
      ring
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hdpos : ∀ k, 0 < Bq (w k) (w k) := fun k => hqpos _ (w.ne_zero k)
  set A : ℚ := ∑ k, max 1 ((L : ℚ) / Bq (w k) (w k)) with hAdef
  set T : ℚ := ∑ i, A * ∑ k, |w k i| with hTdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => le_trans zero_le_one (le_max_left _ _)
  have hcoord : ∀ v, Bq v v ≤ L → ∀ i, |v i| ≤ T := by
    intro v hv i
    have hc : ∀ k, |w.repr v k| ≤ A := by
      intro k
      have h1 : (w.repr v k) ^ 2 * Bq (w k) (w k) ≤ L := by
        rw [hexp] at hv
        refine le_trans ?_ hv
        exact Finset.single_le_sum (f := fun k => (w.repr v k) ^ 2 * Bq (w k) (w k))
          (fun k _ => mul_nonneg (sq_nonneg _) (hdpos k).le) (Finset.mem_univ k)
      have h2 : |w.repr v k| ≤ max 1 ((L : ℚ) / Bq (w k) (w k)) := by
        rcases le_or_gt (|w.repr v k|) 1 with h | h
        · exact h.trans (le_max_left _ _)
        · refine le_trans ?_ (le_max_right _ _)
          rw [le_div_iff₀ (hdpos k)]
          have h3 : |w.repr v k| ≤ (w.repr v k) ^ 2 := by rw [← sq_abs]; nlinarith
          nlinarith [hdpos k]
      refine h2.trans ?_
      exact Finset.single_le_sum (f := fun k => max 1 ((L : ℚ) / Bq (w k) (w k)))
        (fun k _ => le_trans zero_le_one (le_max_left _ _)) (Finset.mem_univ k)
    have hvi : v i = ∑ k, w.repr v k * w k i := by
      conv_lhs => rw [← w.sum_repr v]
      simp [Finset.sum_apply]
    calc |v i| ≤ ∑ k, |w.repr v k * w k i| := by rw [hvi]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, A * |w k i| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)
      _ = A * ∑ k, |w k i| := (Finset.mul_sum _ _ _).symm
      _ ≤ T := Finset.single_le_sum (f := fun i => A * ∑ k, |w k i|)
          (fun i _ => mul_nonneg hA (Finset.sum_nonneg fun k _ => abs_nonneg _)) (Finset.mem_univ i)
  let ψ : X → Module.Free.ChooseBasisIndex ℤ X → ℤ := fun y i => b.repr y i
  have hψ : Function.Injective ψ := by
    intro y z h
    apply b.repr.injective
    ext i
    exact congrFun h i
  refine ((Set.finite_Icc (fun _ => -⌈T⌉) (fun _ => ⌈T⌉)).preimage hψ.injOn).subset ?_
  intro y hy
  have hy' : Bq (φ y) (φ y) ≤ L := by rw [← hφ]; exact_mod_cast hy
  have h := hcoord _ hy'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).1
    show -⌈T⌉ ≤ b.repr y i
    simp only [φ] at h4
    exact_mod_cast h4
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).2
    show b.repr y i ≤ ⌈T⌉
    simp only [φ] at h4
    exact_mod_cast h4
open scoped BigOperators in
private theorem injective_add_nsmul_of_ne_zero {X : Type} [AddCommGroup X] [Module.Free ℤ X] (a : X) {m : ℕ}
    (hm : m ≠ 0) : Function.Injective (fun χ : X => a + m • χ) := by
  intro x y h
  have h' : m • x = m • y := add_left_cancel h
  apply (Module.Free.chooseBasis ℤ X).repr.injective
  ext i
  have := congrArg (fun z => (Module.Free.chooseBasis ℤ X).repr z i) h'
  simp only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hm) this
open scoped BigOperators in
private theorem tsum_subtype_eq_finsum_mem_of_finite {X M : Type} [AddCommMonoid M] [TopologicalSpace M]
    [T2Space M] (S : Set X) (hS : S.Finite) (g : X → M) : ∑' b : S, g b = ∑ᶠ x ∈ S, g x := by
  have h := Finset.tsum_subtype' hS.toFinset g
  rw [hS.coe_toFinset] at h
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, h]
open scoped BigOperators in
private theorem absSumAt_arcTx_twist_tx {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) {k : ℕ}
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k) (hodd : Odd m)
    (p : N.QT (m ^ 2))
    (hbd : ∀ χ, ‖N.txT m p χ‖ ≤ 1) (u : Cˣ) (hu : ‖(u : C)‖ < 1) :
    _root_.GlobalTheory.BddArc.AbsSumAt (u : C)
      (N.arcTx β.be m p)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  classical
  set a : N.X := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with ha
  set q : N.X → ℤ := fun χ =>
    β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2) with hq
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have hden : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  have hq0 : ∀ χ, 0 ≤ q χ := by
    intro χ
    refine Int.ediv_nonneg ?_ hden.le
    by_cases h : a + m • χ = 0
    · rw [h]; simp
    · exact (β.pos _ h).le
  have hfin : ∀ K : ℤ, {χ | q χ ≤ K}.Finite := by
    intro K
    refine ((finite_setOf_bilin_self_le_of_posDef β.be β.symm β.pos
      ((K + 1) * (2 * (m : ℤ) ^ 2))).preimage (injective_add_nsmul_of_ne_zero a hm0).injOn).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hχ ⊢
    have h1 := Int.lt_mul_ediv_self_add
      (x := β.be (a + m • χ) (a + m • χ)) hden
    have h2 : 2 * (m : ℤ) ^ 2 * (β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2))
        ≤ 2 * (m : ℤ) ^ 2 * K := mul_le_mul_of_nonneg_left hχ hden.le
    linarith
  have hfinS : ∀ n : ℕ, {χ | q χ = n}.Finite := fun n =>
    (hfin n).subset fun χ hχ => le_of_eq hχ
  set Q : N.X → ℕ := fun χ => (q χ).toNat with hQdef
  have hQ : ∀ χ, ((Q χ : ℕ) : ℤ) = q χ := fun χ => Int.toNat_of_nonneg (hq0 χ)
  have hpow : ∀ χ, ((u ^ q χ : Cˣ) : C) = (u : C) ^ Q χ := by
    intro χ
    conv_lhs => rw [← hQ χ]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  set f : N.X → C := fun χ => (u : C) ^ Q χ * N.txT m p χ with hf
  have htw : (N.twist β u).tx m (N.twQ β u hm p)
      = ∑' χ, f χ := by
    unfold _root_.GlobalTheory.Ex.NumD.tx
    refine tsum_congr fun χ => ?_
    rw [N.twist_txT β u m hm hodd p χ]
    exact congrArg (· * N.txT m p χ) (hpow χ)
  have hcoeff' : ∀ n : ℕ, PowerSeries.coeff n (N.arcTx β.be m p)
      = ∑ᶠ χ ∈ {χ | q χ = n}, N.txT m p χ := by
    intro n
    unfold _root_.GlobalTheory.Ex.NumD.arcTx
    rw [PowerSeries.coeff_mk]
    rfl
  have hcn : ∀ n : ℕ,
      ‖PowerSeries.coeff n (N.arcTx β.be m p)‖ ≤ 1 := by
    intro n
    rw [hcoeff', finsum_mem_eq_finite_toFinset_sum _ (hfinS n)]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun χ _ => hbd χ
  have hnorm : ∀ χ, ‖f χ‖ ≤ ‖(u : C)‖ ^ Q χ := fun χ => by
    rw [hf, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hbd χ)
  have hQtend : Filter.Tendsto Q Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun K => Filter.eventually_cofinite.2 ?_
    refine (hfin K).subset fun χ hχ => ?_
    simp only [Set.mem_setOf_eq, not_le] at hχ ⊢
    have := hQ χ
    omega
  have hsum : Summable f := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun χ => norm_nonneg _) hnorm
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu).comp hQtend)
  have hcoeff : ∀ n : ℕ, ∑' b : ↑(Q ⁻¹' {n}), f b =
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n := by
    intro n
    have hset : Q ⁻¹' {n} = {χ | q χ = n} := by
      ext χ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      have := hQ χ
      omega
    have hterm : ∀ b : ↑(Q ⁻¹' {n}), f b = (u : C) ^ n * N.txT m p b := by
      intro b
      have hb : Q b = n := b.2
      rw [hf]
      simp only [hb]
    rw [tsum_congr hterm, tsum_mul_left, hset,
      tsum_subtype_eq_finsum_mem_of_finite _ (hfinS n), hcoeff', mul_comm]
  have hfib := hsum.hasSum.tsum_fiberwise Q
  rw [show (fun n => ∑' b : ↑(Q ⁻¹' {n}), f b) = fun n =>
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n
      from funext hcoeff] at hfib
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) hu)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hcn n)
  · rw [htw]
    exact hfib.tsum_eq
end

set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open scoped BigOperators
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (C : Type) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) (k : ℕ)
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m →
    ∀ (ι : Type) (p : ι → N.QT (m ^ 2)),
    (∀ i χ, ‖N.txT m (p i) χ‖ ≤ 1) → ∀ (F : MvPolynomial ι C),
    MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 →
    ∀ u : Cˣ, ‖(u : C)‖ < 1 →
    MvPolynomial.eval (fun i => (N.twist β u).tx m
      (N.twQ β u hm (p i))) F = 0 := by
  intro C _ _ _ N k β m hm hodd ι p hbd F hF u hu
  have h := _root_.GlobalTheory.BddArc.AbsSumAt.aeval (u := (u : C))
    (fun i => absSumAt_arcTx_twist_tx N β m hm hodd (p i) (hbd i) u hu) F
  rw [hF] at h
  rw [← h.2]
  simp
end _root_.GlobalTheory
