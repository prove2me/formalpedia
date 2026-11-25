-- Prove2me | solution 1 for GlobalTheory.genericSection_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:29.633083+00:00
-- url     : https://prove2.me/submissions/7732bef0-f02c-427c-9faa-c7ad8e612f83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_ExistsMulEqMapOfIsAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace GlobalTheory
open NumberField in
open scoped TensorProduct in
open MvPolynomial in
private lemma mem_span_of_lift_aeval_eq_zero_at_chart_point (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) (y : Fin (N + 1) → Ω) (hy₀ : y j₀ = 1)
    (hy : ∀ k, y (j₀.succAbove k) = x k) (w : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N ⊗[K] Ω)
    (hw : Algebra.TensorProduct.lift (MvPolynomial.aeval (R := K) fun q : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N => _root_.GlobalTheory.sPolyImg j₀ x q)
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω)) (fun _ _ => Commute.all _ _) w
      = 0) :
    w ∈ Ideal.span (Set.range fun i : Fin D =>
      ∑ j, (X (i.succ, j) : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] y j) := by
  set π := Algebra.TensorProduct.lift (MvPolynomial.aeval (R := K) fun q : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N => _root_.GlobalTheory.sPolyImg j₀ x q)
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω)) (fun _ _ => Commute.all _ _)
  set Iq : Ideal (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N ⊗[K] Ω) := Ideal.span (Set.range fun i : Fin D =>
      ∑ j, (X (i.succ, j) : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] y j)
  let σr : MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω →+* _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N ⊗[K] Ω := MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeRight : Ω →ₐ[K] _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N ⊗[K] Ω).toRingHom
    (Sum.elim (fun _ => (X (0, j₀) : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] (1 : Ω))
      (fun ik => (X (ik.1, j₀.succAbove ik.2) : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] (1 : Ω)))
  let σ : MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω →ₐ[K] _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N ⊗[K] Ω :=
    { σr with
      commutes' := fun r => by
        show σr (algebraMap K _ r) = _
        rw [MvPolynomial.algebraMap_apply]
        exact (MvPolynomial.eval₂Hom_C _ _ _).trans
          ((Algebra.TensorProduct.includeRight : Ω →ₐ[K] _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N ⊗[K] Ω).commutes r) }
  have hσX : ∀ s, σ (X s) = Sum.elim (fun _ => (X (0, j₀) : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] (1 : Ω))
      (fun ik => (X (ik.1, j₀.succAbove ik.2) : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] (1 : Ω)) s :=
    fun s => MvPolynomial.eval₂Hom_X' _ _ s
  have hσC : ∀ a : Ω, σ (C a) = (1 : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] a :=
    fun a => MvPolynomial.eval₂Hom_C _ _ a
  have hπX : ∀ q, π ((X q : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] (1 : Ω)) = _root_.GlobalTheory.sPolyImg j₀ x q := by
    intro q
    rw [Algebra.TensorProduct.lift_tmul, aeval_X, map_one, mul_one]
  have hsec : ((Ideal.Quotient.mkₐ K Iq).comp (σ.comp π)) = Ideal.Quotient.mkₐ K Iq := by
    apply Algebra.TensorProduct.ext
    · apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, hπX]
      rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [_root_.GlobalTheory.sPolyImg, hσX]
        · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
          refine Ideal.Quotient.eq.2 ?_
          have hL : ∑ j, (X (i'.succ, j) : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) ⊗ₜ[K] y j ∈ Iq :=
            Ideal.subset_span ⟨i', rfl⟩
          convert Iq.neg_mem hL using 1
          simp [_root_.GlobalTheory.sPolyImg, hσX, hσC, Fin.sum_univ_succAbove _ j, hy₀, hy,
            Algebra.TensorProduct.tmul_mul_tmul, Fin.succ_ne_zero]
          try ring
      · simp [_root_.GlobalTheory.sPolyImg, hσX]
    · ext a
      show Ideal.Quotient.mkₐ K Iq (σ (π (1 ⊗ₜ a))) = Ideal.Quotient.mkₐ K Iq (1 ⊗ₜ a)
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      congr 1
      exact hσC a
  have := congrArg (fun f => f w) hsec
  simp only [AlgHom.comp_apply, hw, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
open NumberField in
open scoped TensorProduct in
open MvPolynomial in
private lemma genericSection_baseChange_surjective_ker_lemma (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D N : ℕ) (j₀ : Fin (N + 1))
    (x : Fin N → Ω) [Algebra (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)]
    [FiniteDimensional (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)] [IsScalarTower K (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)]
    (y : Fin (N + 1) → Ω)
    (hcomp : ∀ p : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N, algebraMap (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)
      (algebraMap (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) p) = _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p)
    (hy₀ : y j₀ = 1) (hy : ∀ k, y (j₀.succAbove k) = x k) :
    let Φ₀ : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N ⊗[K] Ω →ₐ[_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K Ω _)
        fun _ _ => Commute.all _ _
    Function.Surjective Φ₀ ∧ RingHom.ker Φ₀ = Ideal.span (Set.range fun i : Fin D =>
      (∑ j, algebraMap (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (X (i.succ, j)) ⊗ₜ[K] y j :
        _root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N ⊗[K] Ω)) := by
  intro Φ₀
  let P := MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω
  let KTp := _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N
  let KTf := _root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N
  let OmS := _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N
  have hΦ₀ : ∀ (a : KTf) (b : Ω), Φ₀ (a ⊗ₜ b) = algebraMap KTf OmS a * algebraMap Ω OmS b := by
    intro a b
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hsh : (_root_.ReciprocityTheory.ChartRestriction.G.T0.sHom (K := K) j₀ x) = (IsScalarTower.toAlgHom K P OmS).comp
      (MvPolynomial.aeval fun q => _root_.GlobalTheory.sPolyImg j₀ x q) := by
    apply MvPolynomial.algHom_ext
    intro q
    unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom
    rw [aeval_X, AlgHom.comp_apply, aeval_X]
    rfl

  let π : KTp ⊗[K] Ω →ₐ[K] P :=
    Algebra.TensorProduct.lift (MvPolynomial.aeval fun q => _root_.GlobalTheory.sPolyImg j₀ x q)
      (IsScalarTower.toAlgHom K Ω P) fun _ _ => Commute.all _ _
  let ι : KTp ⊗[K] Ω →ₐ[K] KTf ⊗[K] Ω :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K KTp KTf) (AlgHom.id K Ω)
  have hπ : ∀ z, Φ₀ (ι z) = algebraMap P OmS (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [ι, π, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, hΦ₀,
        IsScalarTower.coe_toAlgHom', AlgHom.id_apply, map_mul]
      congr 1
      rw [hcomp, hsh]
      rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  have hinj : Function.Injective (algebraMap P OmS) := IsFractionRing.injective P (FractionRing P)
  have hX : ∀ q, Φ₀ (algebraMap KTp KTf (X q) ⊗ₜ (1 : Ω)) =
      algebraMap P OmS (_root_.GlobalTheory.sPolyImg j₀ x q) := by
    intro q
    rw [hΦ₀, map_one, mul_one, hcomp, hsh, AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · have hrange : ∀ p : P, algebraMap P OmS p ∈ Φ₀.range := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        refine ⟨1 ⊗ₜ a, ?_⟩
        show Φ₀ _ = _
        rw [hΦ₀, map_one, one_mul, IsScalarTower.algebraMap_apply Ω P OmS]
        rfl
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p s hp =>
        rw [map_mul]
        refine mul_mem hp ?_
        rcases s with ⟨⟩ | ⟨i, k⟩
        · refine ⟨algebraMap KTp KTf (X (0, j₀)) ⊗ₜ 1, ?_⟩
          show Φ₀ _ = _
          rw [hX]
          simp [_root_.GlobalTheory.sPolyImg]
        · refine ⟨algebraMap KTp KTf (X (i, j₀.succAbove k)) ⊗ₜ 1, ?_⟩
          show Φ₀ _ = _
          rw [hX]
          simp [_root_.GlobalTheory.sPolyImg]
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := P) (K := FractionRing P) z
    have hb' : algebraMap P OmS b ≠ 0 := fun h =>
      nonZeroDivisors.ne_zero hb (hinj (h.trans (map_zero _).symm))
    have hinv := Subalgebra.inv_mem_of_algebraic (A := Φ₀.range) (x := ⟨_, hrange b⟩)
      (Algebra.IsAlgebraic.isAlgebraic _)
    rw [div_eq_mul_inv]
    exact mul_mem (hrange a) hinv
  · intro z hz
    have hden : ∀ z : KTf ⊗[K] Ω, ∃ c : KTp, c ≠ 0 ∧ ∃ w : KTp ⊗[K] Ω,
        (algebraMap KTp KTf c ⊗ₜ[K] (1 : Ω)) * z = ι w := by
      have e : ∀ a b : KTf, (a * b) ⊗ₜ[K] (1 : Ω) = (a ⊗ₜ[K] (1 : Ω)) * (b ⊗ₜ[K] (1 : Ω)) := by
        intro a b
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
      | tmul a b =>
        obtain ⟨p, q, hq, rfl⟩ :=
          IsFractionRing.div_surjective (A := KTp) (K := FractionRing KTp) a
        refine ⟨q, nonZeroDivisors.ne_zero hq, p ⊗ₜ b, ?_⟩
        have hq' : algebraMap KTp KTf q ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_div_cancel₀ _ hq']
        rfl
      | add z w hz hw =>
        obtain ⟨c₁, hc₁, w₁, h₁⟩ := hz
        obtain ⟨c₂, hc₂, w₂, h₂⟩ := hw
        refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, (c₂ ⊗ₜ 1) * w₁ + (c₁ ⊗ₜ 1) * w₂, ?_⟩
        have h₃ : ∀ c : KTp, ι (c ⊗ₜ (1 : Ω)) = algebraMap KTp KTf c ⊗ₜ (1 : Ω) := fun c => rfl
        simp only [map_add, map_mul]
        rw [← h₁, ← h₂, e, h₃, h₃]
        ring
    obtain ⟨c, hc, w, hw⟩ := hden z
    have hc' : algebraMap KTp KTf c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hπw : π w = 0 := by
      apply hinj
      rw [← hπ, ← hw, map_mul, (RingHom.mem_ker).1 hz, mul_zero, map_zero]
    have hwL := mem_span_of_lift_aeval_eq_zero_at_chart_point K Ω D N j₀ x y hy₀ hy w hπw
    have hιw : ι w ∈ Ideal.span (Set.range fun i : Fin D =>
        (∑ j, algebraMap KTp KTf (X (i.succ, j)) ⊗ₜ[K] y j : KTf ⊗[K] Ω)) := by
      have := Ideal.mem_map_of_mem ι hwL
      rw [Ideal.map_span, ← Set.range_comp] at this
      convert this using 3
      ext i
      simp [ι]
    have hz' : z = ((algebraMap KTp KTf c)⁻¹ ⊗ₜ[K] (1 : Ω)) * ι w := by
      rw [← hw, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hc', one_mul,
        ← Algebra.TensorProduct.one_def, one_mul]
    rw [hz']
    exact Ideal.mul_mem_left _ _ hιw
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sum]
    have h : ∀ j, Φ₀ (algebraMap KTp KTf (X (i.succ, j)) ⊗ₜ[K] y j) =
        algebraMap P OmS (_root_.GlobalTheory.sPolyImg j₀ x (i.succ, j) * C (y j)) := by
      intro j
      rw [hΦ₀, hcomp, hsh, map_mul, AlgHom.comp_apply, aeval_X,
        IsScalarTower.algebraMap_apply Ω P OmS]
      rfl
    rw [Finset.sum_congr rfl fun j _ => h j, ← map_sum]
    refine (congrArg (algebraMap P OmS) ?_).trans (map_zero _)
    simp [Fin.sum_univ_succAbove _ j₀, _root_.GlobalTheory.sPolyImg, hy₀, hy, Fin.succ_ne_zero]
end GlobalTheory
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open NumberField
open scoped TensorProduct
open MvPolynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (K Ω K' : Type) [Field K] [Field Ω] [Algebra K Ω] (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) [Algebra (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)] [FiniteDimensional (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)] [Field K'] [Algebra K K'] [Algebra (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K'] [IsScalarTower K (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K'] (T : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N → K') (y : Fin (N + 1) → Ω), (∀ p : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N, algebraMap (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (algebraMap (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) p) = _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ q, T q = algebraMap (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' (algebraMap (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (MvPolynomial.X q))) → y j₀ = 1 → (∀ k, y (j₀.succAbove k) = x k) → ∃ Φ : K' ⊗[K] Ω →+* K' ⊗[_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N, (∀ (a : K') (b : Ω), Φ (a ⊗ₜ[K] b) = a ⊗ₜ[_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) b) ∧ Function.Surjective Φ ∧ RingHom.ker Φ = Ideal.span (Set.range fun i : Fin D => (∑ j, T (i.succ, j) ⊗ₜ[K] y j : K' ⊗[K] Ω)) ∧ IsUnit (Φ (∑ j, T (0, j) ⊗ₜ[K] y j : K' ⊗[K] Ω)) := by
  intro K Ω K' _ _ _ D N j₀ x _ _ _ _ _ _ T y hcomp hT hy₀ hy
  haveI : IsScalarTower K (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) := IsScalarTower.of_algebraMap_eq
    fun r => by
      rw [IsScalarTower.algebraMap_apply K (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) r, hcomp,
        AlgHom.commutes]
  obtain ⟨hsurj, hker⟩ := genericSection_baseChange_surjective_ker_lemma K Ω D N j₀ x y hcomp hy₀ hy
  set Φ₀ : _root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N ⊗[K] Ω →ₐ[_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K Ω _)
        fun _ _ => Commute.all _ _ with hΦ₀
  let e := Algebra.TensorProduct.cancelBaseChange K (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' K' Ω
  let M := Algebra.TensorProduct.map (AlgHom.id (_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K') Φ₀
  have hMs : Function.Surjective M :=
    LinearMap.lTensor_surjective K' (g := Φ₀.toLinearMap) hsurj
  refine ⟨M.toRingHom.comp e.symm.toRingHom, fun a b => ?_, hMs.comp e.symm.surjective, ?_, ?_⟩
  · simp [e, M, Φ₀]
  · have hk : RingHom.ker (M.toRingHom.comp e.symm.toRingHom) =
        Ideal.map e.toRingHom (RingHom.ker M.toRingHom) := by
      rw [← RingHom.comap_ker]
      exact (Ideal.map_comap_of_equiv e.toRingEquiv).symm
    rw [hk]
    have hM : RingHom.ker M.toRingHom = RingHom.ker M := rfl
    rw [hM, Algebra.TensorProduct.lTensor_ker _ hsurj, hker, Ideal.map_span, Ideal.map_span,
      ← Set.range_comp, ← Set.range_comp]
    congr 1
    ext i
    simp [e, hT, Algebra.algebraMap_eq_smul_one]
  · have hform : ∀ (a : K') (b : Ω), (M.toRingHom.comp e.symm.toRingHom) (a ⊗ₜ[K] b) =
        a ⊗ₜ[_root_.ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) b := by
      intro a b
      simp [e, M, Φ₀]
    have hw : (∑ j, _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom (K := K) j₀ x (X (0, j)) * algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (y j)) ≠ 0 := by
      have hP : (∑ j, _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom (K := K) j₀ x (X (0, j)) * algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (y j)) =
          algebraMap (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)
            (∑ j, _root_.GlobalTheory.sPolyImg j₀ x (0, j) * C (y j)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom
        rw [aeval_X, map_mul]
        unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg
        congr 1
      rw [hP]
      intro h
      have h' : (∑ j, _root_.GlobalTheory.sPolyImg j₀ x (0, j) * C (y j) :
          MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) = 0 :=
        IsFractionRing.injective (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω)
          (FractionRing (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω)) (h.trans (map_zero _).symm)
      have h'' := congrArg (MvPolynomial.eval (Sum.elim (fun _ => (1 : Ω)) 0)) h'
      simp [Fin.sum_univ_succAbove _ j₀, _root_.GlobalTheory.sPolyImg, hy₀] at h''
    have hsum : (M.toRingHom.comp e.symm.toRingHom) (∑ j, T (0, j) ⊗ₜ[K] y j) =
        Algebra.TensorProduct.includeRight
          (∑ j, _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom (K := K) j₀ x (X (0, j)) * algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (y j)) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hform, hT, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← hcomp,
        Algebra.smul_def]
      rfl
    rw [hsum]
    exact (isUnit_iff_ne_zero.2 hw).map _
end _root_.GlobalTheory
end GlobalTheory
