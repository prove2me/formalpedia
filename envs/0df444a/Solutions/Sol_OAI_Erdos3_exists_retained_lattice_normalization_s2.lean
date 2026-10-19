-- Prove2me | solution 1 for OAI.Erdos3.exists_retained_lattice_normalization_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:19:34.612688+00:00
-- url     : https://prove2.me/submissions/0cfd4084-6a4b-4810-b481-c011c3b837ad

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B195

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedRefiltering
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_retained_symbol_splitting (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (U : J → LieSubalgebra ℚ F.AssociatedGraded) (v : J → ι → F.AssociatedGraded)
      (n : J → ℕ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.SymbolFactorizationIn b ω hF T
        (F.realPolynomialSymbolHom b ω hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ (∀ j, n j ∣ m) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hF (fun _ => 1)
          (F.realPolynomialSymbolHom b ω hF (fun _ => 1) p₀).coord) ∈
            realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_pointwise_polynomial_symbol_splitting s 1
  refine ⟨2 * K, by omega, ?_⟩
  intro σ ι J L _ _ _ _ _ F b ω hF U v n p hp hι hσ hJ hstructure hv hU hheight hn hnp T hT g hfactor
  classical
  choose E P R hprod hE hR hP using hfactor
  let l := ∏ j, n j
  have hl : 0 < l := Finset.prod_pos (fun j _ => hn j)
  have hdvd (j : J) : n j ∣ l := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let q := p ^ 2 + p + 2
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hq : 0 ≤ q := hp.trans hpq
  have hq1 : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ (2 * K) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    dsimp [q]
    nlinarith
  have hlq : (l : ℝ) ≤ Real.exp q :=
    (product_denominator_le_budget n hp hJ hnp).trans
      (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hq1)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hslow : ∀ j, F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp ((q + 2) ^ 1)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hF (fun _ => 1) T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (by simpa only [pow_one] using hpq.trans (by linarith : q ≤ q + 2))
  have hrat : ∀ j, F.SymbolRationalGrid b ω hF (fun _ => 1) l (R j) :=
    fun j => F.symbolRationalGrid_mono b ω hF (fun _ => 1) (hn j) (hdvd j) (R j) (hR j)
  obtain ⟨m₀, e₀, p₀, r₀, hm₀, hm₀q, hlm, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) U v hv hU H l q hH hl hq
      (hι.trans hpq) (hσ.trans hpq) (hι.trans hpq) (hJ.trans hpq) hHq hlq
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun j i k => rationalHeightLE_ceil_exp (hheight j i k)) T
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hT i)) g E P R hprod
      (fun j => (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) (U j) _).mp (hP j))
      hslow hrat
  refine ⟨m₀, e₀, p₀, r₀, hm₀, hm₀q.trans (Real.exp_le_exp.mpr hcost),
    (fun j => (hdvd j).trans hlm), hepr, hmid, ?_, hr, he0, hr0, hp0⟩
  intro α i
  exact (he α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
    (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_retained_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ F.AssociatedGraded) (v : J → ι → F.AssociatedGraded)
      (n : J → ℕ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.SymbolFactorizationIn b w hF T
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin (Fintype.card ι) → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v₀ i) k) ≤
          ((p + 2) ^ 2 + 2) ^ 63 + 1) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ (∀ j, n j ∣ m) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
          (F.realPolynomialSymbolHom b w hF (fun _ => 1) p₀).coord) ∈
            realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∧
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∀ t : σ → ℝ, eval₂ t (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
            realificationLieSubalgebra (F.gradedRefiltrationSubalgebra (⨅ j, U j))) := by
  obtain ⟨C, hC, hcommon⟩ := exists_retained_symbol_splitting s
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ _ F b w hF U v n p hp hι hσ hJ hstructure hv hU hheight hn hnp T hT g hfactor
  obtain ⟨m, e₀, p₀, r₀, hm, hmp, hnm, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hcommon F b w hF U v n p hp hι hσ hJ hstructure hv hU hheight hn hnp T hT g hfactor
  obtain ⟨v₀, hv₀, hheight₀⟩ := exists_intersection_spanning_logHeight
    (F.associatedGradedBasis b w hF) U v hv hp hι hι hJ hheight
  have hW : BasisGradedSubmodule (F.associatedGradedBasis b w hF) w (⨅ j, U j).toSubmodule := by
    intro k x hx
    apply (lieSubalgebra_mem_iInf U _).mpr
    intro j
    exact hU j k x ((lieSubalgebra_mem_iInf U x).mp hx j)
  refine ⟨v₀, m, e₀, p₀, r₀, hv₀, hW, hheight₀, hm, hmp, hnm, hepr,
    hmid, he, hr, he0, hr0, hp0, ?_⟩
  intro hzero
  exact F.pointwise_refiltered_values_mem b w hF (fun _ => 1) (⨅ j, U j)
    (fun _ => Nat.zero_lt_one) p₀.coord (hp0.trans hzero) hmid

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedLatticeNormalization
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_retained_lattice_normalization_s2_oai (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n : J → ℕ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) := by
  obtain ⟨c, _, hnormalize⟩ := exists_native_polynomial_normalization s
  obtain ⟨k, _, hcommon⟩ := exists_retained_refiltered_factorization s
  obtain ⟨l, _, hleft⟩ := exists_native_slow_left_constant_bound s
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let F : Polynomial ℕ := (Polynomial.X + 2) ^ k
  let H : Polynomial ℕ := ((Polynomial.X + 2) ^ 2 + 2) ^ 63 + 1
  let Q : Polynomial ℕ := Polynomial.X + N + F
  let P : Polynomial ℕ := F + H + (Q + Polynomial.C l) ^ l
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ D w hF U v n p hp hD hσ hJ hv hU hvheight hn hnp A hA g hfactor
  let q := p + (p + c) ^ c + (p + 2) ^ k
  have hn0 : 0 ≤ (p + c) ^ c := by positivity
  have hf0 : 0 ≤ (p + 2) ^ k := by positivity
  have hh0 : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 + 1 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hfq : (p + 2) ^ k ≤ q := by dsimp [q]; linarith
  have hb : (p + 2) ^ k + (((p + 2) ^ 2 + 2) ^ 63 + 1) + (q + l) ^ l ≤ (p + C) ^ C := by
    simpa [P, Q, N, F, H, q, Polynomial.eval₂_pow] using hbudget p hp
  have hl0 : 0 ≤ (q + l) ^ l := by positivity
  have hfC : (p + 2) ^ k ≤ (p + C) ^ C := by linarith
  have hhC : ((p + 2) ^ 2 + 2) ^ 63 + 1 ≤ (p + C) ^ C := by linarith
  have hlC : (q + l) ^ l ≤ (p + C) ^ C := by linarith
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  obtain ⟨a, κ, g₀, ha, hκ, hnormalizeEq, hg₀zero, hsymbol⟩ :=
    hnormalize D w hF (fun _ : σ => 1) p hp hD g
  have hfactor₀ : ∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g₀) p (n j) (U j) := by
    intro j
    rw [hsymbol]
    exact hfactor j
  obtain ⟨v₀, m, e₀, b, R, hv₀, hW, hheight, hm, hmp, hnm, hebr,
      hmid, he, hR, _, hR0, hb0, hvalues⟩ :=
    hcommon D.filtration D.basis w hF U v n p hp
      (by simpa only [Fintype.card_fin] using hD.1) hσ hJ (fun i j k => hD.2.2.1 i j k)
      hv hU hvheight hn hnp A (fun i => (Real.exp_le_exp.mpr hfC).trans (hA i)) g₀ hfactor₀
  let E := D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) a * e₀
  have hE : D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A
      (Real.exp ((p + C) ^ C)) E := by
    have hsmall := hleft D w hF q hq (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
      (hσ.trans hpq) A hApos a (fun i => (ha i).trans (Real.exp_le_exp.mpr hnq)) e₀
      (D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos (Real.exp_le_exp.mpr hfq) e₀ he)
    exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos
      (Real.exp_le_exp.mpr hlC) E hsmall
  have hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g := by
    calc
      _ = D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) a *
          (e₀ * b * R) * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ := by
        simp only [E, mul_assoc]
      _ = g := by rw [hebr]; exact hnormalizeEq
  let e := Fintype.equivFin (Fin d)
  have hrange : Set.range (fun i => v₀ (e i)) = Set.range v₀ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective i
      exact ⟨j, congrArg v₀ hj⟩
  have hv' : Submodule.span ℚ (Set.range (fun i => v₀ (e i))) = (⨅ j, U j).toSubmodule := by
    rw [hrange]
    exact hv₀
  refine ⟨(fun i => v₀ (e i)), m, κ, E, b, R, hv', hW,
    (fun i j => (hheight (e i) j).trans hhC), hm,
    hmp.trans (Real.exp_le_exp.mpr hfC), hnm, hκ, hprod, hE, hR,
    hb0.trans hg₀zero, hR0, ?_, hvalues hg₀zero⟩
  exact (D.filtration.real_symbol_values_iff_refiltration_coefficients D.basis w hF
    (fun _ => 1) (⨅ j, U j) b.coord).mp hmid

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.exists_retained_lattice_normalization_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.exists_retained_lattice_normalization_s2_oai.{u_1, u_2, u_3}
