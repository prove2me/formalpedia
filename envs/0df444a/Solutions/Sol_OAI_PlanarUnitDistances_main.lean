-- Prove2me | solution 1 for OAI.PlanarUnitDistances.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T03:04:36.576271+00:00
-- url     : https://prove2.me/submissions/0654ff6d-2dcb-4622-a978-1abe0615a995

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000
import Theorems.Thm_OAI_PlanarUnitDistances_AlgebraicObstruction_no_rectangles
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceBand_choose
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceScale_scale_limit
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceSequence_diagonal_sequence

section
-- module Solutions.OAIQ2_Uni.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances

theorem unitPairCount_le_card_sq (X : Finset Plane) :
    unitPairCount X ≤ X.card ^ 2 := by
  classical
  calc
    unitPairCount X ≤ X.sym2.card := Finset.card_filter_le _ _
    _ ≤ (X ×ˢ X).card := by
      rw [Finset.sym2_eq_image]
      exact Finset.card_image_le
    _ = X.card ^ 2 := by rw [Finset.card_product, pow_two]

private theorem attainable_nonempty (n : ℕ) :
    {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = m}.Nonempty := by
  obtain ⟨X, hX⟩ := Infinite.exists_subset_card_eq Plane n
  exact ⟨unitPairCount X, X, hX, rfl⟩

private theorem attainable_bddAbove (n : ℕ) :
    BddAbove {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = m} := by
  refine ⟨n ^ 2, ?_⟩
  rintro m ⟨X, hX, rfl⟩
  simpa [hX] using unitPairCount_le_card_sq X

theorem exists_maximizer (n : ℕ) :
    ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = u n :=
  Nat.sSup_mem (attainable_nonempty n) (attainable_bddAbove n)

theorem u_le_sq (n : ℕ) : u n ≤ n ^ 2 := by
  obtain ⟨X, hX, hmax⟩ := exists_maximizer n
  rw [← hmax, ← hX]
  exact unitPairCount_le_card_sq X

@[simp] theorem u_zero : u 0 = 0 := Nat.eq_zero_of_le_zero (by simpa using u_le_sq 0)

@[simp] theorem u_one : u 1 = 0 := by
  obtain ⟨X, hX, hmax⟩ := exists_maximizer 1
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hX
  simpa using hmax.symm

theorem arbitrarily_large_counterexample (hmain : ¬ MainClaim)
    (β : ℝ) (hβ : 1 ≤ β) (hβ' : β < (4 : ℝ) / 3) (N : ℕ) :
    ∃ X : Finset Plane, N ≤ X.card ∧
      (X.card : ℝ) ^ β < (unitPairCount X : ℝ) := by
  classical
  let C : ℝ := (N + 1 : ℝ) ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hfail : ¬ ∀ n : ℕ, (u n : ℝ) ≤ C * (n : ℝ) ^ β := by
    intro hb
    exact hmain ⟨C, β, hC, hβ, hβ', hb⟩
  push Not at hfail
  obtain ⟨n, hn⟩ := hfail
  have hn0 : n ≠ 0 := by
    intro heq
    simp only [heq, Nat.cast_zero, u_zero] at hn
    rw [Real.zero_rpow (by linarith : β ≠ 0), mul_zero] at hn
    exact (lt_irrefl 0) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hrpow : 1 ≤ (n : ℝ) ^ β := Real.one_le_rpow hn1 (by linarith)
  have hnN : N ≤ n := by
    by_contra h
    have hnN' : (n : ℝ) ≤ N + 1 := by exact_mod_cast (by omega : n ≤ N + 1)
    have hnsq : (n : ℝ) ^ 2 ≤ (N + 1 : ℝ) ^ 2 := by
      exact sq_le_sq₀ (by positivity) (by positivity) |>.mpr hnN'
    have hu : (u n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast u_le_sq n
    have hmul : C ≤ C * (n : ℝ) ^ β := by nlinarith [hC]
    dsimp [C] at hmul hn
    nlinarith
  have hC1 : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (N + 1 : ℝ)]
  have hsmall : (n : ℝ) ^ β ≤ C * (n : ℝ) ^ β := by
    exact le_mul_of_one_le_left (by positivity) hC1
  obtain ⟨X, hX, hmax⟩ := exists_maximizer n
  exact ⟨X, hX ▸ hnN, by simpa [hX, hmax] using hsmall.trans_lt hn⟩

theorem counterexample_sequence (hmain : ¬ MainClaim) :
    ∃ X : ℕ → Finset Plane, ∀ j : ℕ, j ≤ (X j).card ∧
      ((X j).card : ℝ) ^ ((4 : ℝ) / 3 - 1 / (j + 3 : ℝ)) <
        (unitPairCount (X j) : ℝ) := by
  classical
  have h (j : ℕ) : ∃ X : Finset Plane, j ≤ X.card ∧
      (X.card : ℝ) ^ ((4 : ℝ) / 3 - 1 / (j + 3 : ℝ)) < (unitPairCount X : ℝ) := by
    apply arbitrarily_large_counterexample hmain
    · have hj : (3 : ℝ) ≤ (j : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) j]
      have hinv : 1 / (j + 3 : ℝ) ≤ 1 / 3 := by
        exact one_div_le_one_div_of_le (by norm_num) hj
      linarith
    · have hj : 0 < 1 / (j + 3 : ℝ) := by positivity
      linarith
  exact ⟨fun j => (h j).choose, fun j => (h j).choose_spec⟩

end PlanarUnitDistances

namespace PlanarUnitDistances.AlgebraicSpecialization
open Set Filter Polynomial
open scoped Topology

lemma signs_in_nhds {f : ℝ → ℝ} {θ d : ℝ} (hf : HasDerivAt f d θ)
    (hd : d ≠ 0) (hz : f θ = 0) {V : Set ℝ} (hV : V ∈ 𝓝 θ) :
    (∃ a ∈ V, f a < 0) ∧ (∃ b ∈ V, 0 < f b) := by
  constructor
  · by_contra h
    push Not at h
    have hm : IsLocalMin f θ := by
      change ∀ᶠ x in 𝓝 θ, f θ ≤ f x
      exact mem_of_superset hV (fun x hx => by simpa [hz] using h x hx)
    exact hd (hm.hasDerivAt_eq_zero hf)
  · by_contra h
    push Not at h
    have hm : IsLocalMax f θ := by
      change ∀ᶠ x in 𝓝 θ, f x ≤ f θ
      exact mem_of_superset hV (fun x hx => by simpa [hz] using h x hx)
    exact hd (hm.hasDerivAt_eq_zero hf)

theorem dense_parameter_root {A B : Type*} [TopologicalSpace A]
    {φ : B → A} (hφ : DenseRange φ) {F : A × ℝ → ℝ} (hF : Continuous F)
    {u : A} {θ d : ℝ} (hf : HasDerivAt (fun t => F (u,t)) d θ)
    (hd : d ≠ 0) (hz : F (u,θ) = 0) {W : Set (A × ℝ)}
    (hW : W ∈ 𝓝 (u,θ)) :
    ∃ v : B, ∃ τ : ℝ, (φ v,τ) ∈ W ∧ F (φ v,τ) = 0 ∧
      ∃ a : ℝ, F (φ v,a) < 0 := by
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨⟨a,ha,haF⟩,⟨b,hb,hbF⟩⟩ := signs_in_nhds hf hd hz
    (Metric.ball_mem_nhds θ hε)
  have hca : Continuous (fun v : A => F (v,a)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hcb : Continuous (fun v : A => F (v,b)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hna : {v : A | F (v,a) < 0} ∈ 𝓝 u :=
    (isOpen_lt hca continuous_const).mem_nhds haF
  have hpb : {v : A | 0 < F (v,b)} ∈ 𝓝 u :=
    (isOpen_lt continuous_const hcb).mem_nhds hbF
  obtain ⟨v,hvU,hva,hvb⟩ := hφ.mem_nhds (inter_mem hU (inter_mem hna hpb))
  have hc : Continuous (fun t => F (φ v,t)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  obtain ⟨τ,hτ,hτF⟩ := intermediate_value_uIcc hc.continuousOn
    (show 0 ∈ uIcc (F (φ v,a)) (F (φ v,b)) by
      rw [uIcc_of_le (hva.le.trans hvb.le)]; exact ⟨hva.le,hvb.le⟩)
  have hτball : τ ∈ Metric.ball θ ε := by
    rw [Real.ball_eq_Ioo] at ha hb ⊢
    rw [mem_uIcc] at hτ
    rcases hτ with hτ | hτ
    · exact ⟨ha.1.trans_le hτ.1,hτ.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hτ.1,hτ.2.trans_lt ha.2⟩
  exact ⟨v,τ,hUV ⟨hvU,hεV hτball⟩,hτF,a,hva⟩

lemma continuous_parameter_eval {ι : Type*} (F : ParameterPolynomial ι) :
    Continuous (fun p : (ι → ℝ) × ℝ => evaluate F p.1 p.2) := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    ext x
    simp [evaluate,eval₂_add]
  | monomial n c =>
    have he : Continuous (fun u : ι → ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) u c) := by
      simpa only [← MvPolynomial.eval_map] using
        (MvPolynomial.continuous_eval (c.map (algebraMap ℚ ℝ)))
    convert (he.comp continuous_fst).mul (continuous_snd.pow n) using 1
    ext x
    simp [evaluate,eval₂_monomial]

theorem rational_simple_root {ι : Type*} (F : ParameterPolynomial ι)
    {u : ι → ℝ} {θ : ℝ} (hz : evaluate F u θ = 0)
    (hd : evaluate F.derivative u θ ≠ 0) {W : Set ((ι → ℝ) × ℝ)}
    (hW : W ∈ 𝓝 (u,θ)) :
    ∃ v : ι → ℚ, ∃ τ : ℝ, ((fun i => (v i : ℝ)),τ) ∈ W ∧
      evaluate F (fun i => (v i : ℝ)) τ = 0 ∧ IsAlgebraic ℚ τ := by
  have hf : HasDerivAt (fun t => evaluate F u t) (evaluate F.derivative u θ) θ := by
    simpa [evaluate,eval₂_eq_eval_map,derivative_map] using
      (F.map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u)).hasDerivAt θ
  have hφ : DenseRange (fun v : ι → ℚ => (fun i => (v i : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨v,τ,hτW,hτF,a,ha⟩ := dense_parameter_root hφ
    (continuous_parameter_eval F) hf hd hz hW
  refine ⟨v,τ,hτW,hτF,?_⟩
  let G : Polynomial ℚ := F.map (MvPolynomial.eval v)
  have he (t : ℝ) : G.aeval t = evaluate F (fun i => (v i : ℝ)) t := by
    simp only [G,aeval_def,eval₂_map,evaluate]
    congr 1
    ext i <;> simp
  refine ⟨G,?_,?_⟩
  · intro hG
    have hh := he a
    rw [hG,map_zero] at hh
    linarith
  · rw [he,hτF]

lemma evaluate_rat {ι : Type*} (F : ParameterPolynomial ι) (v : ι → ℚ) (τ : ℝ) :
    evaluate F (fun i => (v i : ℝ)) τ =
      Polynomial.aeval τ (F.map (MvPolynomial.eval v)) := by
  simp only [aeval_def,eval₂_map,evaluate]
  congr 1
  ext i <;> simp

lemma algebraic_polynomial_value (p : Polynomial ℚ) {τ : ℝ}
    (hτ : IsAlgebraic ℚ τ) : IsAlgebraic ℚ (Polynomial.aeval τ p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n c =>
    simpa only [aeval_monomial] using (isAlgebraic_algebraMap (A := ℝ) c).mul (hτ.pow n)

lemma algebraic_parameter_value {ι : Type*} (F : ParameterPolynomial ι)
    (v : ι → ℚ) {τ : ℝ} (hτ : IsAlgebraic ℚ τ) :
    IsAlgebraic ℚ (evaluate F (fun i => (v i : ℝ)) τ) := by
  rw [evaluate_rat]
  exact algebraic_polynomial_value _ hτ

theorem specialize_chart {ι κ η : Type*} [Finite κ] [Finite η]
    (F : ParameterPolynomial ι) (N D : κ → ParameterPolynomial ι)
    (G J : η → ParameterPolynomial ι) (b : η → MvPolynomial ι ℚ)
    {u : ι → ℝ} {θ : ℝ} (hz : evaluate F u θ = 0)
    (hd : evaluate F.derivative u θ ≠ 0)
    (hD : ∀ i, evaluate (D i) u θ ≠ 0)
    (hb : ∀ j, MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (b j) ≠ 0)
    (hId : ∀ j, Polynomial.C (b j)*G j = F*J j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ι → ℚ, ∃ τ : ℝ, IsAlgebraic ℚ τ ∧
      evaluate F (fun i => (v i : ℝ)) τ = 0 ∧
      (∀ i, evaluate (D i) (fun j => (v j : ℝ)) τ ≠ 0 ∧
        IsAlgebraic ℚ (chartValue N D ((fun j => (v j : ℝ)),τ) i) ∧
        |chartValue N D ((fun j => (v j : ℝ)),τ) i-chartValue N D (u,θ) i| < ε) ∧
      (∀ j, evaluate (G j) (fun i => (v i : ℝ)) τ = 0) := by
  have hden : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ i,
      evaluate (D i) p.1 p.2 ≠ 0 :=
    eventually_all.mpr (fun i => (continuous_parameter_eval (D i)).continuousAt.eventually_ne (hD i))
  have happ : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ i,
      |chartValue N D p i-chartValue N D (u,θ) i| < ε := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun p => chartValue N D p i) (u,θ) :=
      (continuous_parameter_eval (N i)).continuousAt.div
        (continuous_parameter_eval (D i)).continuousAt (hD i)
    have he := hc.eventually (Metric.ball_mem_nhds (chartValue N D (u,θ) i) hε)
    simpa only [Metric.mem_ball,Real.dist_eq] using he
  have hbne : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ j,
      evaluate (Polynomial.C (b j)) p.1 p.2 ≠ 0 := by
    apply eventually_all.mpr
    intro j
    apply (continuous_parameter_eval (Polynomial.C (b j))).continuousAt.eventually_ne
    simpa [evaluate] using hb j
  obtain ⟨v,τ,hW,hF,hτ⟩ := rational_simple_root F hz hd (hden.and (happ.and hbne))
  refine ⟨v,τ,hτ,hF,?_,?_⟩
  · intro i
    refine ⟨hW.1 i,?_,hW.2.1 i⟩
    unfold chartValue
    rw [div_eq_mul_inv]
    exact (algebraic_parameter_value (N i) v hτ).mul
      (IsAlgebraic.inv_iff.mpr (algebraic_parameter_value (D i) v hτ))
  · intro j
    have he := congrArg (Polynomial.eval₂RingHom
      (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (fun i => (v i : ℝ))) τ) (hId j)
    change evaluate (Polynomial.C (b j)*G j) _ τ = evaluate (F*J j) _ τ at he
    simp only [evaluate,eval₂_mul] at he
    change evaluate (Polynomial.C (b j)) _ τ * evaluate (G j) _ τ =
      evaluate F _ τ * evaluate (J j) _ τ at he
    rw [hF,zero_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (hW.2.2 j)

end PlanarUnitDistances.AlgebraicSpecialization

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField

theorem finite_coordinates_primitive {K : Type*} [Field K] [CharZero K]
    [Algebra K ℝ] {κ : Type*} [Finite κ] (x : κ → ℝ)
    (hx : ∀ i, IsAlgebraic K (x i)) :
    ∃ θ : ℝ, IsAlgebraic K θ ∧ ∀ i, ∃ p q : Polynomial K,
      Polynomial.aeval θ q ≠ 0 ∧ x i = Polynomial.aeval θ p / Polynomial.aeval θ q := by
  let M := IntermediateField.adjoin K (Set.range x)
  have : Finite (Set.range x) := Set.finite_range x
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin
    (fun y hy => by obtain ⟨i,rfl⟩ := hy; exact (hx i).isIntegral)
  obtain ⟨θ,hθ⟩ := Field.exists_primitive_element K M
  refine ⟨(θ : ℝ),?_,?_⟩
  · exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom M.val
  · intro i
    by_cases hi : x i = 0
    · exact ⟨0,1,by simp,by simp [hi]⟩
    let y : M := ⟨x i,IntermediateField.subset_adjoin K (Set.range x) (mem_range_self i)⟩
    have hm : y ∈ IntermediateField.adjoin K {θ} := by rw [hθ]; trivial
    obtain ⟨p,q,hpq⟩ := (IntermediateField.mem_adjoin_simple_iff K y).mp hm
    have he : x i = Polynomial.aeval (θ : ℝ) p / Polynomial.aeval (θ : ℝ) q := by
      have hh := congrArg (fun a : M => (a : ℝ)) hpq
      simpa [y] using hh
    refine ⟨p,q,?_,he⟩
    intro hq
    rw [hq,div_zero] at he
    exact hi he

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Polynomial

theorem clear_polynomial {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (f : R →+* K)
    (hfrac : ∀ a : K, ∃ r s : R, s ≠ 0 ∧ a * f s = f r)
    (p : Polynomial K) :
    ∃ q : Polynomial R, ∃ d : R, d ≠ 0 ∧ q.map f = C (f d) * p := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁,d₁,hd₁,hq₁⟩ := h₁
    obtain ⟨q₂,d₂,hd₂,hq₂⟩ := h₂
    refine ⟨C d₂ * q₁ + C d₁ * q₂,d₁*d₂,mul_ne_zero hd₁ hd₂,?_⟩
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,hq₁,hq₂,
      map_mul]
    ring
  | monomial n a =>
    obtain ⟨r,s,hs,he⟩ := hfrac a
    refine ⟨monomial n r,s,hs,?_⟩
    rw [Polynomial.map_monomial,← he,mul_comm a (f s),← C_mul_monomial]

theorem clear_relation {R K L : Type*} [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra K L]
    (f : R →+* K) (hf : Function.Injective f)
    (hfrac : ∀ a : K, ∃ r s : R, s ≠ 0 ∧ a * f s = f r)
    (θ : L) (F : Polynomial R) (d : R) (hd : d ≠ 0)
    (hF : F.map f = C (f d) * minpoly K θ)
    (G : Polynomial R) (hG : Polynomial.aeval θ (G.map f) = 0) :
    ∃ b : R, ∃ J : Polynomial R, b ≠ 0 ∧ C b * G = F * J := by
  obtain ⟨H,hH⟩ := minpoly.dvd K θ hG
  obtain ⟨J,e,he,hJ⟩ := clear_polynomial f hfrac H
  refine ⟨d*e,J,mul_ne_zero hd he,?_⟩
  apply Polynomial.map_injective f hf
  simp only [Polynomial.map_mul,Polynomial.map_C,map_mul,hF,hJ,hH]
  ring

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField

theorem parameterMap_injective {ι : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) : Function.Injective (parameterMap u) := by
  intro p q hpq
  apply (algebraicIndependent_iff_injective_aeval.mp hu)
  simpa only [coe_parameterMap] using congrArg (fun a : ParameterField u => (a : ℝ)) hpq

theorem parameterMap_fraction {ι : Type*} (u : ι → ℝ) (a : ParameterField u) :
    ∃ r s : MvPolynomial ι ℚ, s ≠ 0 ∧ a * parameterMap u s = parameterMap u r := by
  by_cases ha : a = 0
  · exact ⟨0,1,one_ne_zero,by simp [ha]⟩
  obtain ⟨r,hr,s,hs,h⟩ := IntermediateField.mem_adjoin_iff_div.mp a.property
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨r,rfl⟩ := hr
  obtain ⟨s,rfl⟩ := hs
  change (a : ℝ) = MvPolynomial.aeval u r / MvPolynomial.aeval u s at h
  have hsne : MvPolynomial.aeval u s ≠ 0 := by
    intro hz
    rw [hz,div_zero] at h
    exact ha (Subtype.ext h)
  refine ⟨r,s,?_,?_⟩
  · intro hz
    exact hsne (by rw [hz,map_zero])
  · apply Subtype.ext
    change (a : ℝ) * ((parameterMap u s : ParameterField u) : ℝ) =
      ((parameterMap u r : ParameterField u) : ℝ)
    rw [coe_parameterMap,coe_parameterMap,h]
    exact div_mul_cancel₀ _ hsne

theorem cleared_minpoly {ι : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) {θ : ℝ}
    (hθ : IsAlgebraic (ParameterField u) θ) :
    ∃ F : AlgebraicSpecialization.ParameterPolynomial ι, ∃ d : MvPolynomial ι ℚ,
      d ≠ 0 ∧
      F.map (parameterMap u).toRingHom =
        C (parameterMap u d) * minpoly (ParameterField u) θ ∧
      AlgebraicSpecialization.evaluate F u θ = 0 ∧
      AlgebraicSpecialization.evaluate F.derivative u θ ≠ 0 := by
  obtain ⟨F,d,hd,hF⟩ := clear_polynomial (parameterMap u).toRingHom
    (parameterMap_fraction u) (minpoly (ParameterField u) θ)
  have hev (p : AlgebraicSpecialization.ParameterPolynomial ι) :
      Polynomial.aeval θ (p.map (parameterMap u).toRingHom) =
        AlgebraicSpecialization.evaluate p u θ := by
    have hcomp : (algebraMap (ParameterField u) ℝ).comp (parameterMap u).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u :=
      RingHom.ext (fun p => coe_parameterMap u p)
    simp only [Polynomial.aeval_def,Polynomial.eval₂_map,AlgebraicSpecialization.evaluate,hcomp]
  have hdn : ((parameterMap u d : ParameterField u) : ℝ) ≠ 0 := by
    intro h
    apply hd
    apply parameterMap_injective hu
    apply Subtype.ext
    simpa only [map_zero,ZeroMemClass.coe_zero] using h
  refine ⟨F,d,hd,hF,?_,?_⟩
  · rw [← hev,hF,map_mul,minpoly.aeval (ParameterField u) θ,mul_zero]
  · have hs : (minpoly (ParameterField u) θ).Separable :=
      (minpoly.irreducible hθ.isIntegral).separable
    have hm := hs.aeval_derivative_ne_zero (minpoly.aeval (ParameterField u) θ)
    have hder := congrArg Polynomial.derivative hF
    rw [Polynomial.derivative_map,Polynomial.derivative_C_mul] at hder
    rw [← hev,hder,map_mul,Polynomial.aeval_C]
    exact mul_ne_zero hdn hm

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField AlgebraicSpecialization

lemma evaluate_as_map {ι : Type*} (u : ι → ℝ) (p : ParameterPolynomial ι) (θ : ℝ) :
    Polynomial.aeval θ (p.map (parameterMap u).toRingHom) = evaluate p u θ := by
  have hcomp : (algebraMap (ParameterField u) ℝ).comp (parameterMap u).toRingHom =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u :=
    RingHom.ext (fun p => coe_parameterMap u p)
  simp only [Polynomial.aeval_def,Polynomial.eval₂_map,evaluate,hcomp]

theorem coordinate_polynomials {ι κ : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) (θ : ℝ) (x : κ → ℝ)
    (hx : ∀ i, ∃ p q : Polynomial (ParameterField u),
      Polynomial.aeval θ q ≠ 0 ∧ x i = Polynomial.aeval θ p / Polynomial.aeval θ q) :
    ∃ N D : κ → ParameterPolynomial ι,
      (∀ i, evaluate (D i) u θ ≠ 0) ∧ ∀ i, chartValue N D (u,θ) i = x i := by
  classical
  have hi (i : κ) : ∃ N D : ParameterPolynomial ι,
      evaluate D u θ ≠ 0 ∧ evaluate N u θ / evaluate D u θ = x i := by
    obtain ⟨p,q,hq,hx⟩ := hx i
    obtain ⟨P,d,hd,hP⟩ := clear_polynomial (parameterMap u).toRingHom
      (parameterMap_fraction u) p
    obtain ⟨Q,e,he,hQ⟩ := clear_polynomial (parameterMap u).toRingHom
      (parameterMap_fraction u) q
    have hn (a : MvPolynomial ι ℚ) (ha : a ≠ 0) :
        ((parameterMap u a : ParameterField u) : ℝ) ≠ 0 := by
      intro hz
      apply ha
      apply parameterMap_injective hu
      apply Subtype.ext
      simpa using hz
    have hPd : evaluate P u θ = ((parameterMap u d : ParameterField u) : ℝ) *
        Polynomial.aeval θ p := by
      rw [← evaluate_as_map,hP,map_mul,Polynomial.aeval_C]
      rfl
    have hQe : evaluate Q u θ = ((parameterMap u e : ParameterField u) : ℝ) *
        Polynomial.aeval θ q := by
      rw [← evaluate_as_map,hQ,map_mul,Polynomial.aeval_C]
      rfl
    have hC (a : MvPolynomial ι ℚ) : evaluate (C a) u θ =
        ((parameterMap u a : ParameterField u) : ℝ) := by
      rw [coe_parameterMap]
      simp only [evaluate,Polynomial.eval₂_C]
      rfl
    have hmul (a b : ParameterPolynomial ι) : evaluate (a*b) u θ =
        evaluate a u θ * evaluate b u θ := Polynomial.eval₂_mul _ _
    refine ⟨C e*P,C d*Q,?_,?_⟩
    · rw [hmul]
      rw [hC,hQe]
      exact mul_ne_zero (hn d hd) (mul_ne_zero (hn e he) hq)
    · rw [hmul,hmul,hC,hC,hPd,hQe,hx]
      have hdR := hn d hd
      have heR := hn e he
      rw [mul_left_comm ((parameterMap u d : ParameterField u) : ℝ)
        ((parameterMap u e : ParameterField u) : ℝ),← mul_assoc,← mul_assoc]
      exact mul_div_mul_left _ _ (mul_ne_zero heR hdR)
  choose N D hD hv using hi
  exact ⟨N,D,hD,hv⟩

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField AlgebraicSpecialization

lemma cleared_unit_equation {K : Type*} [Field K]
    (a b c d e f g h : K) (hb : b ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0) (hh : h ≠ 0) :
    (a*d-c*b)^2*(f*h)^2 + (e*h-g*f)^2*(b*d)^2 - (b*d)^2*(f*h)^2 = 0 ↔
      (a/b-c/d)^2+(e/f-g/h)^2 = 1 := by
  have hid : (a*d-c*b)^2*(f*h)^2 + (e*h-g*f)^2*(b*d)^2 - (b*d)^2*(f*h)^2 =
      ((a/b-c/d)^2+(e/f-g/h)^2-1)*((b*d)^2*(f*h)^2) := by
    field_simp
  rw [hid,mul_eq_zero]
  have hprod : (b*d)^2*(f*h)^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero hb hd)) (pow_ne_zero _ (mul_ne_zero hf hh))
  simp only [hprod,or_false,sub_eq_zero]

lemma evaluate_unitRelation {ι κ : Type*} (N D : κ × Fin 2 → ParameterPolynomial ι)
    (u : ι → ℝ) (θ : ℝ) (hD : ∀ k, evaluate (D k) u θ ≠ 0) (i j : κ) :
    evaluate (unitRelation N D i j) u θ = 0 ↔ unitEquation (chartValue N D (u,θ)) i j := by
  simp only [unitRelation,evaluate,eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,
    unitEquation,chartValue]
  exact cleared_unit_equation _ _ _ _ _ _ _ _ (hD (i,0)) (hD (j,0)) (hD (i,1)) (hD (j,1))

theorem algebraic_unit_approximation {κ : Type*} [Finite κ]
    (x : κ × Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : κ × Fin 2 → ℝ, (∀ k, IsAlgebraic ℚ (y k) ∧ |y k-x k| < ε) ∧
      ∀ i j, unitEquation x i j → unitEquation y i j := by
  classical
  obtain ⟨s,hs⟩ := exists_isTranscendenceBasis ℚ ℝ
  let u : s → ℝ := Subtype.val
  have hu : AlgebraicIndependent ℚ u := hs.1
  have : Algebra.IsAlgebraic (ParameterField u) ℝ := hs.isAlgebraic_field
  obtain ⟨θ,hθ,hx⟩ := finite_coordinates_primitive x
    (fun k => Algebra.IsAlgebraic.isAlgebraic (x k) : ∀ k, IsAlgebraic (ParameterField u) (x k))
  obtain ⟨F,d,hd,hF,hz,hder⟩ := cleared_minpoly hu hθ
  obtain ⟨N,D,hD,hval⟩ := coordinate_polynomials hu θ x hx
  let η := {e : κ × κ // unitEquation x e.1 e.2}
  let G : η → ParameterPolynomial s := fun e => unitRelation N D e.val.1 e.val.2
  have hG (e : η) : Polynomial.aeval θ ((G e).map (parameterMap u).toRingHom) = 0 := by
    rw [evaluate_as_map]
    apply (evaluate_unitRelation N D u θ hD _ _).mpr
    simpa only [unitEquation,hval] using e.property
  have hId (e : η) : ∃ b : MvPolynomial s ℚ, ∃ J : ParameterPolynomial s,
      b ≠ 0 ∧ C b*G e = F*J :=
    clear_relation (parameterMap u).toRingHom (parameterMap_injective hu)
      (parameterMap_fraction u) θ F d hd hF (G e) (hG e)
  choose b J hb hId using hId
  have hbval (e : η) : MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (b e) ≠ 0 := by
    intro he
    exact hb e ((algebraicIndependent_iff_injective_aeval.mp hu)
      (show MvPolynomial.aeval u (b e) = MvPolynomial.aeval u 0 by
        simpa only [map_zero,MvPolynomial.aeval_def] using he))
  obtain ⟨v,τ,_,_,hcoord,hunit⟩ := specialize_chart F N D G J b hz hder hD hbval hId hε
  refine ⟨chartValue N D ((fun i => (v i : ℝ)),τ),?_,?_⟩
  · intro k
    exact ⟨(hcoord k).2.1,by simpa only [hval] using (hcoord k).2.2⟩
  · intro i j hij
    exact (evaluate_unitRelation N D _ τ (fun k => (hcoord k).1) i j).mp
      (hunit ⟨(i,j),hij⟩)

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Filter
open scoped Topology

lemma plane_dist_sq (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0-q 0)^2+(p 1-q 1)^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [WithLp.ofLp_sub,Pi.sub_apply,Real.norm_eq_abs,sq_abs]

lemma plane_unit_iff {κ : Type*} (p : κ → EuclideanSpace ℝ (Fin 2)) (i j : κ) :
    dist (p i) (p j) = 1 ↔ unitEquation (fun k => p k.1 k.2) i j := by
  have he := plane_dist_sq (p i) (p j)
  have hn := dist_nonneg (x := p i) (y := p j)
  unfold unitEquation
  simp only
  constructor <;> intro h <;> nlinarith

lemma plane_close_of_coordinates {δ : ℝ} (hδ : 0 < δ)
    (p q : EuclideanSpace ℝ (Fin 2)) (h : ∀ k, |p k-q k| < δ) :
    dist p q < 2*δ := by
  have h0 := (sq_lt_sq₀ (abs_nonneg (p 0-q 0)) hδ.le).mpr (h 0)
  have h1 := (sq_lt_sq₀ (abs_nonneg (p 1-q 1)) hδ.le).mpr (h 1)
  rw [sq_abs] at h0 h1
  have he := plane_dist_sq p q
  nlinarith [dist_nonneg (x := p) (y := q)]

lemma finite_separation {κ : Type*} [Finite κ] {M : Type*} [MetricSpace M]
    (p : κ → M) (hp : Function.Injective p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i j, i ≠ j → ρ < dist (p i) (p j) := by
  have he : ∀ᶠ ρ : ℝ in 𝓝 0, ∀ i j, i ≠ j → ρ < dist (p i) (p j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hd : (0 : ℝ) < dist (p i) (p j) := dist_pos.mpr (hp.ne hij)
      have hlt : Iio (dist (p i) (p j)) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hd
      exact Filter.mem_of_superset hlt (fun _ h _ => h)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r/2,by positivity,hball ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < r/2)]
  linarith

theorem algebraic_planar_specialization {κ : Type*} [Finite κ]
    (p : κ → EuclideanSpace ℝ (Fin 2)) (hp : Function.Injective p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : κ → EuclideanSpace ℝ (Fin 2), Function.Injective q ∧
      (∀ i, dist (q i) (p i) < ε ∧ ∀ k, IsAlgebraic ℚ (q i k)) ∧
      ∀ i j, dist (p i) (p j) = 1 → dist (q i) (q j) = 1 := by
  classical
  obtain ⟨ρ,hρ,hsep⟩ := finite_separation p hp
  let δ := min (ε/3) (ρ/6)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨y,hy,heq⟩ := algebraic_unit_approximation (fun k => p k.1 k.2) hδ
  let q : κ → EuclideanSpace ℝ (Fin 2) := fun i => WithLp.toLp 2 (fun k => y (i,k))
  have hclose (i : κ) : dist (q i) (p i) < 2*δ :=
    plane_close_of_coordinates hδ _ _ (fun k => (hy (i,k)).2)
  have hερ : 2*δ < ε := by have := min_le_left (ε/3) (ρ/6); dsimp [δ]; linarith
  have hρδ : 4*δ < ρ := by have := min_le_right (ε/3) (ρ/6); dsimp [δ]; linarith
  refine ⟨q,?_,?_,?_⟩
  · intro i j hij
    by_contra hne
    have hdist := dist_triangle (p i) (q i) (p j)
    rw [dist_comm (p i) (q i)] at hdist
    have hi := hclose i
    have hj := hclose j
    have hs := hsep i j hne
    rw [← hij] at hj
    linarith
  · intro i
    exact ⟨(hclose i).trans hερ,fun k => (hy (i,k)).1⟩
  · intro i j h
    exact (plane_unit_iff q i j).mpr (heq i j ((plane_unit_iff p i j).mp h))

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances

theorem unitPairCount_map_mono {α : Type*} (s : Finset α)
    (e f : α ↪ Plane) (hunit : ∀ i j, dist (e i) (e j) = 1 → dist (f i) (f j) = 1) :
    unitPairCount (s.map e) ≤ unitPairCount (s.map f) := by
  classical
  simp only [unitPairCount,Finset.sym2_map,Finset.filter_map,Finset.card_map]
  apply Finset.card_le_card
  intro a ha
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,?_⟩
  have h := (Finset.mem_filter.mp ha).2
  induction a using Sym2.ind with
  | _ i j => exact hunit i j h

theorem algebraic_set_specialization (X : Finset Plane) :
    ∃ Y : Finset Plane, Y.card = X.card ∧ unitPairCount X ≤ unitPairCount Y ∧
      ∀ p ∈ Y, ∀ k, IsAlgebraic ℚ (p k) := by
  classical
  obtain ⟨q,hq,ha,hu⟩ := PrimitiveChart.algebraic_planar_specialization
    (fun p : X => (p : Plane)) Subtype.val_injective (show (0 : ℝ) < 1 by norm_num)
  let e : X ↪ Plane := ⟨q,hq⟩
  let v : X ↪ Plane := ⟨Subtype.val,Subtype.val_injective⟩
  have hv : (Finset.univ : Finset X).map v = X := by
    ext p
    simp [v]
  refine ⟨Finset.univ.map e,?_,?_,?_⟩
  · simp
  · have hm := unitPairCount_map_mono Finset.univ v e hu
    rw [hv] at hm
    exact hm
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hp
    exact (ha i).2

theorem algebraic_counterexample_sequence (hmain : ¬ MainClaim) :
    ∃ X : ℕ → Finset Plane, ∀ j : ℕ, j ≤ (X j).card ∧
      ((X j).card : ℝ)^((4 : ℝ)/3-1/(j+3 : ℝ)) < (unitPairCount (X j) : ℝ) ∧
      ∀ p ∈ X j, ∀ k, IsAlgebraic ℚ (p k) := by
  classical
  obtain ⟨X,hX⟩ := counterexample_sequence hmain
  choose Y hcard hcount halg using fun j => algebraic_set_specialization (X j)
  refine ⟨Y,fun j => ?_⟩
  rw [hcard]
  exact ⟨(hX j).1,(hX j).2.trans_le (Nat.cast_le.mpr (hcount j)),halg j⟩

end PlanarUnitDistances

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Powers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PowerGrowth
open Filter

variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma Upper.mono (hg : Upper F t g a) (h : f ≤ᶠ[F] g) : Upper F t f a := by
  intro ε hε
  filter_upwards [hg ε hε,h] with i hi hfg
  exact hfg.trans hi

lemma Upper.congr (hf : Upper F t f a) (h : f =ᶠ[F] g) : Upper F t g a :=
  hf.mono h.symm.le

lemma eventually_one_le (ht : Tendsto t F atTop) : ∀ᶠ i in F,1 ≤ t i :=
  ht.eventually_ge_atTop 1

lemma eventually_base_pos (ht : Tendsto t F atTop) : ∀ᶠ i in F,0 < t i :=
  (eventually_one_le ht).mono fun _ hi => lt_of_lt_of_le zero_lt_one hi

lemma eventually_constant_le_rpow (ht : Tendsto t F atTop) {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ i in F,C ≤ t i ^ ε := by
  exact (_root_.tendsto_rpow_atTop hε |>.comp ht).eventually_ge_atTop C

lemma Lower.const_mul (hf : Lower F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 < C) : Lower F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C⁻¹,eventually_base_pos ht] with i hi hc hti
  have hc' : 1 ≤ C*(t i)^(ε/2) := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hC).mp hc
  have he : a-ε/2=(a-ε)+ε/2 := by ring
  have hpos := Real.rpow_nonneg hti.le (a-ε)
  calc
    (t i)^(a-ε) ≤ (t i)^(a-ε)*(C*(t i)^(ε/2)) := le_mul_of_one_le_right hpos hc'
    _ = C*(t i)^(a-ε/2) := by
      conv_rhs => rw [he,Real.rpow_add hti]
      ring
    _ ≤ C*f i := mul_le_mul_of_nonneg_left hi hC.le

end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma upper_rpow (ht : Tendsto t F atTop) (a : ℝ) :
    Upper F t (fun i => t i^a) a := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)

lemma diagonal {R : ℕ → ℕ → Prop} (hR : ∀k,∀ᶠn in atTop,R k n) :
    ∃f : ℕ → ℕ,Tendsto f atTop atTop ∧ ∀n,R n (f n) := by
  have h : ∀k,∃N,∀n≥N,R k n := fun k => eventually_atTop.mp (hR k)
  choose N hN using h
  refine ⟨fun n => max n (N n),tendsto_atTop_mono (fun n => le_max_left n (N n)) tendsto_id,?_⟩
  intro n
  exact hN n _ (le_max_right _ _)
end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances
open Filter CircleIncidence PowerGrowth
open scoped Classical
noncomputable section

lemma unordered_le_incidences (X : Finset Plane) :
    (unitPairCount X:ℝ) ≤ CircleIncidence.incidences X X := by
  have hc : unitPairCount X ≤ ((X×ˢX).filter (fun pq => dist pq.1 pq.2=1)).card := by
    unfold unitPairCount
    rw [Finset.sym2_eq_image,Finset.filter_image]
    apply Finset.card_image_le.trans
    apply le_of_eq
    congr 1
  apply (Nat.cast_le.mpr hc).trans_eq
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Finset.sum_product,CircleIncidence.incidences,CircleIncidence.degree_sum,dist_comm]

theorem counterexample_power_sequence (hmain : ¬MainClaim) :
    ∃(t : ℕ → ℝ) (X : ℕ → Finset Plane),
      Tendsto t atTop atTop ∧ (∀i,1≤t i) ∧ (∀i,(X i).Nonempty) ∧
      (∀i,((X i).card:ℝ)=(t i)^3) ∧
      Upper atTop t (fun i => ((X i).card:ℝ)) 3 ∧
      Lower atTop t (fun i => CircleIncidence.incidences (X i) (X i)) 4 ∧
      (∀i,∀p∈X i,∀k,IsAlgebraic ℚ (p k)) := by
  obtain ⟨Y,hY⟩ := algebraic_counterexample_sequence hmain
  let X : ℕ → Finset Plane := fun i => Y (i+1)
  let t : ℕ → ℝ := fun i => ((X i).card:ℝ)^((1:ℝ)/3)
  have hcard (i : ℕ) : (i:ℝ)+1≤((X i).card:ℝ) := by
    exact_mod_cast (hY (i+1)).1
  have hcard1 (i : ℕ) : (1:ℝ)≤((X i).card:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) i,hcard i]
  have hn : Tendsto (fun i => ((X i).card:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun i => (by linarith [hcard i] : (i:ℝ)≤((X i).card:ℝ)))
      tendsto_natCast_atTop_atTop
  have ht : Tendsto t atTop atTop := (_root_.tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp hn
  have ht1 (i : ℕ) : 1≤t i := Real.one_le_rpow (hcard1 i) (by norm_num)
  have hx0 (i : ℕ) : (X i).Nonempty := Finset.card_pos.mp (by
    have hh := (hY (i+1)).1
    dsimp [X]
    omega)
  have heq (i : ℕ) : ((X i).card:ℝ)=(t i)^3 := by
    dsimp [t]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hu : Upper atTop t (fun i => ((X i).card:ℝ)) 3 := by
    apply (upper_rpow ht 3).congr
    exact Eventually.of_forall fun i => by simpa only [Real.rpow_ofNat] using (heq i).symm
  have hl : Lower atTop t (fun i => CircleIncidence.incidences (X i) (X i)) 4 := by
    intro ε hε
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun i:ℕ => (i:ℝ)) atTop atTop).eventually_ge_atTop (3/ε)] with i hi
    have hden : 0<(i:ℝ)+4 := by positivity
    have hinv : 1/((i:ℝ)+4)≤ε/3 := by
      apply (div_le_iff₀ hden).mpr
      have hh := (div_le_iff₀ hε).mp hi
      nlinarith
    have hexp : (1/3:ℝ)*(4-ε)≤4/3-1/((i:ℝ)+4) := by linarith
    have hp := Real.rpow_le_rpow_of_exponent_le (hcard1 i) hexp
    have hh := (hY (i+1)).2.1
    have hh' : ((X i).card:ℝ)^(4/3-1/((i:ℝ)+4)) < (unitPairCount (X i):ℝ) := by
      convert hh using 1; simp [X,Nat.cast_add]; ring_nf
    have hl' := hp.trans (hh'.le.trans (unordered_le_incidences (X i)))
    simpa only [t,←Real.rpow_mul (Nat.cast_nonneg (X i).card)] using hl'
  exact ⟨t,X,ht,ht1,hx0,heq,hu,hl,fun i => (hY (i+1)).2.2⟩
end
end PlanarUnitDistances

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Cross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma avg_congr (μ : Law X) {f g : X → ℝ} (h : ∀ x, f x = g x) : avg μ f = avg μ g := by
  unfold avg
  exact sum_congr rfl (fun x _ => congrArg (μ.val x * ·) (h x))
lemma avg_ite (μ : Law X) (P : X → Prop) [DecidablePred P] :
    avg μ (fun x => if P x then 1 else 0) = event μ P := by
  unfold event
  apply avg_congr
  intro x
  split_ifs <;> rfl

lemma avg_const (μ : Law X) (c : ℝ) : avg μ (fun _ => c) = c := by
  simp [avg,← sum_mul,μ.total]
lemma avg_add (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x+g x)=avg μ f+avg μ g := by simp [avg,mul_add,sum_add_distrib]
lemma avg_mono (μ : Law X) {f g : X  →  ℝ} (h : ∀ x,f x ≤ g x) : avg μ f ≤ avg μ g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x)
lemma event_mono (μ : Law X) {P Q : X  →  Prop} (h : ∀ x,P x → Q x) : event μ P ≤ event μ Q := by
  classical
  apply avg_mono; intro x; split_ifs <;> simp_all
lemma event_union_le (μ : Law X) (P Q : X  →  Prop) :
    event μ (fun x => P x ∨ Q x) ≤ event μ P+event μ Q := by
  classical
  unfold event
  rw [← avg_add]
  apply avg_mono; intro x; split_ifs <;> simp_all

lemma pair_avg (μ : Law X) (ν : Law Y) (f : X×Y → ℝ) :
    avg (pair μ ν) f=avg μ (fun x => avg ν (fun y => f (x,y))) := by
  simp [avg,pair,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma pair_fst (μ : Law X) (ν : Law Y) (f : X → ℝ) :
    avg (pair μ ν) (fun x => f x.1)=avg μ f := by
  rw [pair_avg]; simp_rw [avg_const]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
open scoped Classical
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma atom_le_fiber (μ : Law X) (φ : X → Y) (x : X) : μ.val x ≤ fiberMass μ φ (φ x) := by
  classical
  rw [fiberMass_eq]
  have h := single_le_sum (s := univ) (f := fun y => if φ y=φ x then μ.val y else 0)
    (fun y _ => by split_ifs <;> simp [μ.nonneg]) (mem_univ x)
  simpa using h

lemma push_avg (μ : Law X) (φ : X → Y) (g : Y → ℝ) :
    avg (push μ φ) g = avg μ (fun x => g (φ x)) := by
  classical
  unfold avg push
  simp only [fiberMass_eq,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp

omit [Fintype Y] in
lemma cond_weight (μ : Law X) (φ : X → Y) (y : Y) (x : X) :
    fiberMass μ φ y * (cond μ φ y).val x = if φ x=y then μ.val x else 0 := by
  classical
  by_cases hy : 0 < fiberMass μ φ y
  · simp only [cond,hy,↓reduceDIte]
    split_ifs
    · field_simp
    · ring
  · have hz := le_antisymm (le_of_not_gt hy) (fiberMass_nonneg μ φ y)
    simp only [hz,zero_mul]
    split_ifs with hxy
    · have h := atom_le_fiber μ φ x
      rw [hxy,hz] at h
      exact (le_antisymm h (μ.nonneg x)).symm
    · rfl

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma cond_tower_dep (μ : Law X) (φ : X → Y) (f : Y → X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) (f y)) = avg μ (fun x => f (φ x) x) := by
  classical
  unfold avg
  simp only [push,mul_sum,← mul_assoc,cond_weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw StarScore CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

lemma col_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (right π) (fun q => avg (col π q) (fun p => f p q)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [col,push_avg]
  change avg (push π Prod.snd) _ = _
  exact cond_tower_dep π Prod.snd (fun q pq => f pq.1 q)
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.WedgeProfiles
open RareScore CrossStructure FiniteLaw
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma edge_residual (r b : Bool) (l x y : A×B) :
    |value b-(1-value r+sign r*(ind (exceptional r l x)+ind (exceptional r l y)))| ≤
      2*(ind (exceptional r l x ∧ exceptional r l y)+ind (¬Consistent b x y)) := by
  cases r <;> cases b <;>
    simp only [value,sign,Bool.false_eq_true,ite_false,ite_true,exceptional,Consistent]
  all_goals
    by_cases hx : x.1=l.1
    <;> by_cases hy : y.1=l.1
    <;> by_cases hx' : x.2=l.2
    <;> by_cases hy' : y.2=l.2
    <;> by_cases he : x.1=y.1
    <;> by_cases he' : x.2=y.2
    <;> simp_all [ind]
    <;> norm_num

lemma wedge_residual (r b c : Bool) (l x y z : A×B) :
    |value b-value c-sign r*(ind (exceptional r l x)-ind (exceptional r l z))| ≤
      2*(ind (exceptional r l x ∧ exceptional r l y)+ind (exceptional r l z ∧ exceptional r l y)+
        ind (¬Consistent b x y)+ind (¬Consistent c z y)) := by
  have hb := edge_residual r b l x y
  have hc := edge_residual r c l z y
  have he : value b-value c-sign r*(ind (exceptional r l x)-ind (exceptional r l z))=
      (value b-(1-value r+sign r*(ind (exceptional r l x)+ind (exceptional r l y))))-
      (value c-(1-value r+sign r*(ind (exceptional r l z)+ind (exceptional r l y)))) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

lemma wedge_size (r b c : Bool) (l x y z : A×B) :
    ind (exceptional r l x)+ind (exceptional r l z)-
      2*(ind (exceptional r l x ∧ exceptional r l z)+
        ind (exceptional r l x ∧ exceptional r l y)+ind (exceptional r l z ∧ exceptional r l y)+
        ind (¬Consistent b x y)+ind (¬Consistent c z y)) ≤ |value b-value c| := by
  have hh := wedge_residual r b c l x y z
  have he : |sign r*(ind (exceptional r l x)-ind (exceptional r l z))|=
      ind (exceptional r l x)+ind (exceptional r l z)-2*ind (exceptional r l x ∧ exceptional r l z) := by
    cases r <;> by_cases hx : exceptional false l x <;> by_cases hz : exceptional false l z
    <;> by_cases hx' : exceptional true l x <;> by_cases hz' : exceptional true l z
    <;> simp_all [sign,ind]
    <;> norm_num
  have ht := abs_sub_le (sign r*(ind (exceptional r l x)-ind (exceptional r l z))) (value b-value c) 0
  rw [sub_zero,sub_zero,abs_sub_comm (sign r*_) (value b-value c),he] at ht
  linarith
end
end PlanarUnitDistances.WedgeProfiles

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma event_eq_sum (μ : Law X) (P : X → Prop) :
    event μ P = ∑ x, if P x then μ.val x else 0 := by
  unfold event avg
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp_all

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Wedges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma dependent_avg (μ : Law X) (ν : X → Law Y) (f : X×Y → ℝ) :
    avg (dependent μ ν) f = avg μ (fun x => avg (ν x) (fun y => f (x,y))) := by
  simp [avg,dependent,Fintype.sum_prod_type,mul_sum,mul_assoc]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.WedgeLaw
open FiniteLaw FiniteStarCoupling WedgeProfiles
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma average (π : Law (P×Q)) (f : Q×(P×P) → ℝ) :
    avg (law π) f=avg (right π) (fun q => avg (pair (col π q) (col π q)) (fun pp => f (q,pp))) :=
  dependent_avg _ _ _

lemma first (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (law π) (fun a => f a.2.1 a.1)=avg π (fun pq => f pq.1 pq.2) := by
  rw [average]
  calc
    _ = avg (right π) (fun q => avg (col π q) (fun p => f p q)) := by
      apply avg_congr
      intro q
      exact FiniteLaw.pair_fst (col π q) (col π q) (fun p => f p q)
    _ = _ := col_avg π f

lemma first_point (π : Law (P×Q)) (f : P → ℝ) :
    avg (law π) (fun a => f a.2.1)=avg (left π) f := by
  rw [first π (fun p _ => f p)]
  exact (push_avg π Prod.fst f).symm

end
end PlanarUnitDistances.WedgeLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]
lemma left_val (π : Law (P×Q)) (p : P) : (left π).val p = ∑q,π.val (p,q) := by
  simp only [left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) : (right π).val q = ∑p,π.val (p,q) := by
  simp [right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma col_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (right π).val q*(col π q).val p=π.val (p,q) := by
  simp only [col,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.1=p then fiberMass π Prod.snd q*(cond π Prod.snd q).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma col_val (π : Law (P×Q)) {q : Q} (hq : 0<(right π).val q) (p : P) :
    (col π q).val p=π.val (p,q)/(right π).val q := by
  apply (eq_div_iff hq.ne').mpr
  simpa only [mul_comm] using col_weight π p q
end
end PlanarUnitDistances.FiniteStarCoupling

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceEntropy
open Finset Real FiniteInformation
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype Q] in
lemma degree_nonneg (E : P → Q → Prop) (q : Q) : 0 ≤ degree E q :=
  sum_nonneg fun p _ => indicator_nonneg E p q

theorem wedge_atom (E : P → Q → Prop) {dmin : ℝ}
    (hE : 0 < edgeCount E) (hd : 0 < dmin) (hdeg : ∀ q, dmin ≤ degree E q)
    (hcodeg : ∀ p r, p ≠ r → (∑ q, indicator E p q * indicator E r q) ≤ 2)
    (p r : P) (hpr : p ≠ r) : wedge E (p,r) ≤ 2/(edgeCount E*dmin) := by
  unfold wedge
  calc
    _ ≤ ∑ q, indicator E p q * indicator E r q / (edgeCount E*dmin) := by
      apply sum_le_sum
      intro q _
      exact div_le_div_of_nonneg_left
        (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
        (mul_pos hE hd) (mul_le_mul_of_nonneg_left (hdeg q) hE.le)
    _ = (∑ q, indicator E p q * indicator E r q) / (edgeCount E*dmin) := by rw [sum_div]
    _ ≤ 2/(edgeCount E*dmin) := div_le_div_of_nonneg_right (hcodeg p r hpr) (by positivity)

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.UnitCodegree
open Polynomial Complex
open scoped ComplexConjugate

lemma center_linear (p r q : ℂ)
    (hp : (q-p)*(conj q-conj p) = 1)
    (hr : (q-r)*(conj q-conj r) = 1) :
    (p-r)*conj q + (conj p-conj r)*q = p*conj p-r*conj r := by
  linear_combination hr-hp

lemma centerPolynomial_eval (p r q : ℂ)
    (hp : (q-p)*(conj q-conj p) = 1)
    (hr : (q-r)*(conj q-conj r) = 1) :
    (centerPolynomial p r).eval q = 0 := by
  have hl := center_linear p r q hp hr
  simp only [centerPolynomial, eval_sub, eval_mul, eval_X, eval_C]
  linear_combination -(q-p)*hl+(p-r)*hp

lemma centerPolynomial_expansion (p r : ℂ) :
    centerPolynomial p r = C (-(conj p-conj r))*X^2+
      C (p*conj p-r*conj r-(p-r)*conj p+p*(conj p-conj r))*X+
      C (-(p*(p*conj p-r*conj r-(p-r)*conj p))-(p-r)) := by
  simp only [centerPolynomial, map_add, map_sub, map_neg, map_mul]
  ring

lemma centerPolynomial_ne_zero (p r : ℂ) (hpr : p ≠ r) : centerPolynomial p r ≠ 0 := by
  intro hz
  have hh := congrArg (fun f : ℂ[X] => f.coeff 2) hz
  rw [centerPolynomial_expansion] at hh
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_mul_X, coeff_C] at hh
  simp only [ite_true, ite_false, add_zero, coeff_zero] at hh
  exact hpr (star_injective (sub_eq_zero.mp (neg_eq_zero.mp hh)))

lemma centerPolynomial_degree (p r : ℂ) : (centerPolynomial p r).natDegree ≤ 2 := by
  rw [centerPolynomial_expansion]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X_pow]; norm_num)
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X]; norm_num)
  · simp only [natDegree_C]; norm_num

theorem common_centers_card (p r : ℂ) (hpr : p ≠ r) (S : Finset ℂ)
    (hS : ∀ q ∈ S, (q-p)*(conj q-conj p) = 1 ∧ (q-r)*(conj q-conj r) = 1) :
    S.card ≤ 2 := by
  have hh : S.card ≤ (centerPolynomial p r).natDegree :=
    Polynomial.card_le_degree_of_subset_roots ?_
  · exact hh.trans (centerPolynomial_degree p r)
  · intro q hq
    exact (Polynomial.mem_roots (centerPolynomial_ne_zero p r hpr)).mpr
      (centerPolynomial_eval p r q (hS q hq).1 (hS q hq).2)

lemma unit_distance_equation (p q : ℂ) (h : dist p q = 1) :
    (q-p)*(conj q-conj p) = 1 := by
  rw [← map_sub, mul_conj, normSq_eq_norm_sq, ← dist_eq_norm, dist_comm q p, h]
  norm_num

theorem unit_centers_card (p r : ℂ) (hpr : p ≠ r) (S : Finset ℂ)
    (hS : ∀ q ∈ S, dist p q = 1 ∧ dist r q = 1) : S.card ≤ 2 :=
  common_centers_card p r hpr S fun q hq =>
    ⟨unit_distance_equation p q (hS q hq).1, unit_distance_equation r q (hS q hq).2⟩

end PlanarUnitDistances.UnitCodegree

namespace PlanarUnitDistances.IncidenceEntropy
open Finset UnitCodegree
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype P] in

theorem unit_incidence_codegree (E : P → Q → Prop) (x : P → ℂ) (y : Q → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hE : ∀ p q, E p q → dist (x p) (y q) = 1)
    (p r : P) (hpr : p ≠ r) : (∑ q, indicator E p q * indicator E r q) ≤ 2 := by
  classical
  let T : Finset Q := univ.filter fun q => E p q ∧ E r q
  have hs : (∑ q, indicator E p q * indicator E r q) = (T.card : ℝ) := by
    have hh (q : Q) : indicator E p q * indicator E r q =
        if E p q ∧ E r q then (1:ℝ) else 0 := by
      unfold indicator
      split_ifs <;> simp_all
    simp_rw [hh]
    simp [T]
  rw [hs]
  have hc := unit_centers_card (x p) (x r) (fun hh => hpr (hx hh)) (T.image y) ?_
  · rw [Finset.card_image_of_injective _ hy] at hc
    exact_mod_cast hc
  · intro q hq
    obtain ⟨s,hs,hsy⟩ := mem_image.mp hq
    have hss := (mem_filter.mp hs).2
    subst q
    exact ⟨hE p s hss.1,hE r s hss.2⟩

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.UniformGraphLaw
open Finset FiniteLaw FiniteStarCoupling IncidenceEntropy
open scoped Classical BigOperators
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma right_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (q : Q) :
    (right (law E hE)).val q=degree E q/edgeCount E := by
  rw [right_val]
  simp only [law,←sum_div,degree]
lemma left_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (p : P) :
    (left (law E hE)).val p=pointLaw E p := by
  rw [left_val]
  simp only [law,←sum_div,pointLaw]
lemma col_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {q : Q}
    (hq : 0<degree E q) (p : P) :
    (col (law E hE) q).val p=indicator E p q/degree E q := by
  rw [col_val (law E hE) (by rw [right_eq]; exact div_pos hq hE),right_eq]
  change (indicator E p q/edgeCount E)/(degree E q/edgeCount E)=_
  field_simp

lemma wedge_val (E : P → Q → Prop) (hE : 0<edgeCount E)
    (hd : ∀q,0<degree E q) (a : Q×(P×P)) :
    (WedgeLaw.law (law E hE)).val a=
      indicator E a.2.1 a.1*indicator E a.2.2 a.1/(edgeCount E*degree E a.1) := by
  change (right (law E hE)).val a.1*((col (law E hE) a.1).val a.2.1*(col (law E hE) a.1).val a.2.2)=_
  rw [right_eq,col_eq _ _ (hd _),col_eq _ _ (hd _)]
  field_simp

theorem edge_count (E : P → Q → Prop) (hE : 0<edgeCount E)
    {d : ℝ} (hd : 0<d) (hdeg : ∀q,d≤degree E q)
    (hcodeg : ∀p r,p≠r → (∑q,indicator E p q*indicator E r q)≤2)
    (A : Q×(P×P) → Prop) (hA : ∀a,A a → a.2.1≠a.2.2) :
    event (WedgeLaw.law (law E hE)) A ≤
      ((univ.filter (fun pr : P×P => ∃q,A (q,pr))).card:ℝ)*2/(edgeCount E*d) := by
  have hg : ∀q,0<degree E q := fun q => hd.trans_le (hdeg q)
  let B := univ.filter (fun pr : P×P => ∃q,A (q,pr))
  calc
    _ ≤ ∑pr∈B,IncidenceEntropy.wedge E pr := by
      unfold event avg
      rw [Fintype.sum_prod_type,sum_comm]
      dsimp only [B]
      simp only [sum_filter]
      apply sum_le_sum
      intro pr _
      by_cases hb : ∃q,A (q,pr)
      · simp only [hb,↓reduceIte]
        unfold IncidenceEntropy.wedge
        apply sum_le_sum
        intro q _
        rw [wedge_val E hE hg]
        split_ifs
        · simp only [mul_one]
          exact le_rfl
        · simp only [mul_zero]
          exact div_nonneg (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
            (mul_nonneg hE.le (degree_nonneg E _))
      · simp only [hb,↓reduceIte]
        apply le_of_eq
        apply sum_eq_zero
        intro q _
        simp [show ¬A (q,pr) from fun h => hb ⟨q,h⟩]
    _ ≤ (B.card:ℝ)*(2/(edgeCount E*d)) := by
      calc
        _ ≤ ∑pr∈B,2/(edgeCount E*d) := by
          apply sum_le_sum
          intro pr hpr
          obtain ⟨q,hq⟩ := (mem_filter.mp hpr).2
          exact wedge_atom E hE hd hdeg hcodeg pr.1 pr.2 (hA (q,pr) hq)
        _ = _ := by simp
    _ = _ := by ring
end
end PlanarUnitDistances.UniformGraphLaw

namespace PlanarUnitDistances.GeometricLaw
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
lemma row_count (P Q : Finset Plane) (p : P) :
    (∑q,IncidenceEntropy.indicator (E P Q) p q)=CircleIncidence.degree Q p := by
  change (∑q : Q,if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)=_
  rw [CircleIncidence.degree_sum]
  exact (Finset.sum_coe_sort Q (fun q => if dist (p:Plane) q=1 then (1:ℝ) else 0)).trans
    (by simp only [dist_comm])
lemma left_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) :
    (left (graph P Q he)).val p=CircleIncidence.degree Q p/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.left_eq,IncidenceEntropy.pointLaw,edgeCount_eq,row_count]
lemma right_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (q : Q) :
    (right (graph P Q he)).val q=CircleIncidence.degree P q/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.right_eq,degree_eq,edgeCount_eq]
end
end PlanarUnitDistances.GeometricLaw

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f : ι → ℝ} {a b : ℝ}
lemma Upper.power_bound (hf : Upper F t f a) (hab : a < b) :
    ∀ᶠi in F,f i ≤ t i^b := by
  convert hf (b-a) (sub_pos.mpr hab) using 1; ring_nf
end PlanarUnitDistances.PowerGrowth

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sequence
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceSequence
open Filter PowerGrowth CircleIncidence
open scoped Classical
noncomputable section

lemma Good.center_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (q : Q) : 0 < degree P q := by
  have hn : (0:ℝ) < Q.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).2
  have hh := (le_div_iff₀ h.positive).mp (h.atomQ q q.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hn) h.positive).trans_le hh

lemma Sequence.tendsto (s : Sequence) : Tendsto s.t atTop atTop :=
  tendsto_atTop_mono (fun i => (by linarith [s.large i] : (i:ℝ) ≤ s.t i))
    tendsto_natCast_atTop_atTop

lemma Sequence.accuracy_limit : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma Sequence.cardP_power (s : Sequence) : Upper atTop s.t (fun i => ((s.P i).card:ℝ)) 1 := by
  intro ε hε
  filter_upwards [Sequence.accuracy_limit.eventually_le_const hε] with i hi
  exact (s.good i).cardP.trans (Real.rpow_le_rpow_of_exponent_le
    (by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]) (by linarith))

lemma Sequence.wedge_power (s : Sequence) : Lower atTop s.t
    (fun i => incidences (s.P i) (s.Q i)*((27/50:ℝ)*incidences (s.P i) (s.Q i)/(s.Q i).card)/2) 2 := by
  intro ε hε
  filter_upwards [Sequence.accuracy_limit.eventually_le_const hε] with i hi
  exact (Real.rpow_le_rpow_of_exponent_le
    (by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]) (by linarith)).trans (s.good i).wedgeBound

end
end PlanarUnitDistances.IncidenceSequence

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
variable (P Q : Finset Plane)

variable {P Q}

namespace Model
variable (M : Model P Q)
lemma unit_identity (p : P) (q : Q) (h : dist (p:Plane) (q:Plane)=1) :
    (M.z (.inl p)-M.z (.inr q))*(M.w (.inl p)-M.w (.inr q))=1 := by
  apply Subtype.val_injective
  change ((M.z (.inl p):ℂ)-(M.z (.inr q):ℂ))*((M.w (.inl p):ℂ)-(M.w (.inr q):ℂ))=1
  simp only [M.z_eq,M.w_eq,location,Sum.elim_inl,Sum.elim_inr]
  exact UnitCodegree.unit_distance_equation _ _ (by
    rw [UnitCodegree.zCoordinate.dist_map,dist_comm]; exact h)

lemma sub_mem (v r : P⊕Q) : M.z v-M.z r ∈ M.support :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(v,r),Finset.mem_univ _,rfl⟩))
end Model
end
end PlanarUnitDistances.CommonFieldModel

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_AbsoluteValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma abs_log_eq_posLog_add (r : ℝ) : |log r| = log⁺ r + log⁺ r⁻¹ := by
  have h := (half_mul_log_add_log_abs (x := r))
  have h' := (posLog_sub_posLog_inv (x := r))
  linarith

lemma weighted_abs_log_eq_twice {x : K} (_hx : x ≠ 0) :
    ((∑ σ : K →ₐ[ℚ] ℂ, |log (infiniteEntry K σ x)|) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |log (finiteEntry K v.1 v.2 x)|)) /
        (Module.finrank ℚ K : ℝ) = 2 * exactHeight K x := by
  have harch : (∑ σ : K →ₐ[ℚ] ℂ, |log (infiniteEntry K σ x)|) =
    (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
      (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x⁻¹)) := by
    simp only [abs_log_eq_posLog_add, map_inv₀,sum_add_distrib]
  have hfin : (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |log (finiteEntry K v.1 v.2 x)|) =
    (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x⁻¹)) := by
    simp only [abs_log_eq_posLog_add]
    simpa only [map_inv₀] using
      finsum_add_distrib (finite_posLog_support K x) (finite_posLog_support K x⁻¹)
  rw [harch,hfin]
  have := exactHeight_inv K x
  unfold exactHeight at this ⊢
  simp only [add_div] at this ⊢
  linarith

end
end PlanarUnitDistances.WeightedAbsoluteValues

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_States
attribute [-instance] _root_.OAI.PlanarUnitDistances.LevelScale.instIsFiniteMeasureProdPlaceRealMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PlaceLevels
open Finset Real WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

lemma log_off_support {S : Finset K} {x : K} (hx : x∈S)
    {v : Nat.Primes × Gal(K/ℚ)} (hv : v∉finiteSupport K S) :
    log (finiteEntry K v.1 v.2 x)=0 := by
  by_cases h0 : x=0
  · simp [h0]
  have hp : v.1.val ∉ rootDenominators K x ∪ rootDenominators K x⁻¹ := by
    intro hh
    apply hv
    exact mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_subtype.mpr hh,mem_univ _⟩⟩
  rw [finiteEntry_eq_one_off_support K h0 _ _ hp,log_one]

lemma log_le_radius {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    |log (av K v x)|≤radius K S v := by
  exact single_le_sum (fun y _ => abs_nonneg (log (av K v y))) hx
lemma threshold_in_range {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    -radius K S v ≤ -log (av K v x) ∧ -log (av K v x) ≤ radius K S v := by
  have h := abs_le.mp (log_le_radius K hx v)
  constructor <;> linarith
end
end PlanarUnitDistances.PlaceLevels

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma bit_integrableOn (a l u : ℝ) : IntegrableOn (bit a) (Icc l u) := by
  have he : bit a = (Iio a).indicator (fun _ => (1 : ℝ)) := by
    funext s; simp [bit,Set.indicator]
  rw [he]
  exact (show Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc l u))
    from continuous_const.integrableOn_Icc).indicator measurableSet_Iio

lemma abs_bit_sub_eq (a b s : ℝ) :
    |bit a s - bit b s| = (Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) s := by
  by_cases ha : s < a <;> by_cases hb : s < b <;>
    simp [bit,ha,hb,Set.indicator,mem_Ico]

lemma bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hua : a ≤ u)
    (hlb : l ≤ b) (hub : b ≤ u) :
    ∫ s in Icc l u, |bit a s - bit b s| = |a-b| := by
  simp_rw [abs_bit_sub_eq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  rw [measureReal_restrict_apply measurableSet_Ico]
  have hsub : Ico (min a b) (max a b) ⊆ Icc l u := by
    intro s hs
    exact ⟨(le_min hla hlb).trans hs.1, hs.2.le.trans (max_le hua hub)⟩
  rw [inter_eq_left.mpr hsub,Real.volume_real_Ico]
  simp [smul_eq_mul,max_sub_min_eq_abs,abs_sub_comm]

end
end PlanarUnitDistances.ThresholdProfiles

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scale
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceScale
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence
open scoped Classical
noncomputable section
variable (s : Sequence)
lemma positiveQ (n : ℕ) (q : s.Q n) : 0<(right (graph s n)).val q := by
  rw [graph,GeometricLaw.right_eq]
  exact div_pos ((s.good n).center_degree_pos q) (s.good n).positive
lemma support (n : ℕ) (p : s.P n) (q : s.Q n) (h : 0<(graph s n).val (p,q)) :
    GeometricLaw.E (s.P n) (s.Q n) p q := by
  change 0<IncidenceEntropy.indicator (GeometricLaw.E (s.P n) (s.Q n)) p q/_ at h
  by_contra hn
  simp [IncidenceEntropy.indicator,hn] at h
lemma point_bound (n : ℕ) (p : s.P n) : (left (graph s n)).val p≤ s.t n^(-1/2:ℝ) := by
  rw [graph,GeometricLaw.left_eq]
  exact (s.good n).atomUpper p p.property
end
end PlanarUnitDistances.IncidenceScale

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelSnapshot
open MeasureTheory Set Finset FiniteLaw LevelStates PlaceLevels
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

lemma measurable_value {Y : Type*} [MeasurableSpace Y] (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → Y) :
    Measurable (fun a => F (snapshot S z w src tgt u a)) :=
  (measurable_of_finite F).comp (measurable_snapshot S z w src tgt u)

lemma integrable_piece (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → ℝ)
    (v : Place K S) (l r : ℝ) : IntegrableOn (fun s => F (snapshot S z w src tgt u (v,s))) (Icc l r) := by
  apply Integrable.mono' (integrable_const (∑d : Data V E, |F d|))
    ((measurable_value S z w src tgt u F).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using
      (single_le_sum (s:=univ) (fun d _ => abs_nonneg (F d)) (mem_univ (snapshot S z w src tgt u (v,s))))

end
end PlanarUnitDistances.LevelSnapshot

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Integration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLawIntegral
open MeasureTheory Finset FiniteLaw
open scoped Classical
noncomputable section
variable {X Ω : Type*} [Fintype X] [MeasurableSpace Ω]

lemma avg_mono_support (μ : Law X) {f g : X → ℝ}
    (h : ∀x,0<μ.val x → f x ≤ g x) : avg μ f ≤ avg μ g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : μ.val x=0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))) (μ.nonneg x)

end
end PlanarUnitDistances.FiniteLawIntegral

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LocalProfiles
open FiniteLaw FiniteStarCoupling WedgeProfiles RareScore RareMoments ScoreBook LevelScores
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q]

lemma X_nonneg (B : Book D P Q H A) (s : D) (p : P) : 0 ≤ X B s p := by
  unfold X ind
  positivity
lemma error1_nonneg (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : 0 ≤ error1 B s a := by
  unfold error1 jfirst jsecond ifirst isecond ind
  positivity
lemma error2_nonneg (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : 0 ≤ error2 B s a := by
  unfold error2 jpoints jfirst jsecond ifirst isecond ind
  positivity

lemma residual (B : Book D P Q H A) (s : D) (a : Q×(P×P)) :
    |bits B s a-(signed B s a.2.1-signed B s a.2.2)| ≤ error1 B s a := by
  by_cases hc : B.C s
  · simp [error1,signed,X,Book.R,hc,ind]
  · by_cases hg : B.good s
    · have hr : B.R s := ⟨hc,hg⟩
      have he : error1 B s a = 2*(jfirst B s a+jsecond B s a+ifirst B s a+isecond B s a) := by
        simp only [error1,hc,hr,hg,ite_false,ite_true,not_true_eq_false,and_false,ind,zero_add]
      rw [he]
      unfold signed bits
      rw [show X B s a.2.1=ind (exceptional B s (B.point s a.2.1)) from ite_eq_left hr,
        show X B s a.2.2=ind (exceptional B s (B.point s a.2.2)) from ite_eq_left hr,←mul_sub]
      exact wedge_residual (rareBit B s) (B.bit s a.2.1 a.1) (B.bit s a.2.2 a.1)
        (B.label s) (B.point s a.2.1) (B.center s a.1) (B.point s a.2.2)
    · simp only [error1,signed,X,Book.R,hc,hg,not_false_eq_true,true_and,ite_true,ite_false,
        and_false,ind,mul_zero,sub_zero,zero_add,add_zero]
      cases h₁ : B.bit s a.2.1 a.1 <;> cases h₂ : B.bit s a.2.2 a.1 <;> norm_num [bits,value,h₁,h₂]

lemma size (B : Book D P Q H A) (s : D) (a : Q×(P×P)) :
    X B s a.2.1+X B s a.2.2-error2 B s a ≤ |bits B s a| := by
  by_cases h : B.R s
  · simp only [X,error2,h,ite_true]
    exact wedge_size (rareBit B s) (B.bit s a.2.1 a.1) (B.bit s a.2.2 a.1)
      (B.label s) (B.point s a.2.1) (B.center s a.1) (B.point s a.2.2)
  · simp [X,error2,h]
end
end PlanarUnitDistances.LocalProfiles

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
noncomputable section

lemma bit_integral {l u a : ℝ} (hla : l ≤ a) (hau : a ≤ u) :
    (∫s in Icc l u,bit a s)=a-l := by
  have he : bit a = (Iio a).indicator (fun _ => (1:ℝ)) := by
    funext s
    simp [bit,Set.indicator]
  rw [he,integral_indicator_const (1:ℝ) measurableSet_Iio,
    measureReal_restrict_apply measurableSet_Iio]
  have hi : Iio a ∩ Icc l u=Ico l a := by
    ext s
    simp only [mem_inter_iff,mem_Iio,mem_Icc,mem_Ico]
    constructor
    · rintro ⟨hsa,hls,hsu⟩
      exact ⟨hls,hsa⟩
    · rintro ⟨hls,hsa⟩
      exact ⟨hsa,hls,hsa.le.trans hau⟩
  rw [hi,Real.volume_real_Ico]
  simp [smul_eq_mul,max_eq_left (sub_nonneg.mpr hla)]

lemma signed_bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hau : a ≤ u)
    (hlb : l ≤ b) (hbu : b ≤ u) :
    (∫s in Icc l u,bit a s-bit b s)=a-b := by
  rw [integral_sub (bit_integrableOn a l u) (bit_integrableOn b l u),
    bit_integral hla hau,bit_integral hlb hbu]
  ring
end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.ActualProfiles
open MeasureTheory Set FiniteLaw LevelSnapshot ScoreBook ActualScoreBook PlaceLevels
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

namespace Input
variable (G : Input K V P Q H)
lemma piece (F : Data V (P×Q) → ℝ) (v : Place K G.support) :
    IntegrableOn (fun s => F (G.snap (v,s))) (Icc (-radius K G.support v) (radius K G.support v)) :=
  integrable_piece _ _ _ _ _ _ F _ _ _

lemma bits_eq (a : Q×(P×P)) (v : Place K G.support) (s : ℝ) :
    LocalProfiles.bits G.book (G.snap (v,s)) a=
      ThresholdProfiles.bit (G.threshold v a.2.1 a.1) s-
      ThresholdProfiles.bit (G.threshold v a.2.2 a.1) s := by
  simp only [LocalProfiles.bits,book,make,snap,snapshot,LevelStates.bit,
    WedgeProfiles.value,threshold,ThresholdProfiles.bit,decide_eq_true_eq]
  rfl

lemma height_nonneg (p : P) (v : Place K G.support) : 0 ≤ G.heightAt p v :=
  integral_nonneg (fun _ => LocalProfiles.X_nonneg _ _ _)
lemma error_nonneg (i : Bool) (a : Q×(P×P)) (v : Place K G.support) : 0 ≤ G.errorAt i a v := by
  apply integral_nonneg
  intro s
  cases i
  · exact LocalProfiles.error2_nonneg _ _ _
  · exact LocalProfiles.error1_nonneg _ _ _

theorem residual (a : Q×(P×P)) (v : Place K G.support)
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    |G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-
      (G.profile a.2.1 v-G.profile a.2.2 v)| ≤ G.errorAt true a v := by
  have hi := G.piece (fun d => LocalProfiles.bits G.book d a) v
  have h₁i := G.piece (fun d => LocalProfiles.signed G.book d a.2.1) v
  have h₂i := G.piece (fun d => LocalProfiles.signed G.book d a.2.2) v
  have he := G.piece (fun d => LocalProfiles.error1 G.book d a) v
  have h := integral_mono (hi.sub (h₁i.sub h₂i)).abs he
    (fun s => LocalProfiles.residual G.book (G.snap (v,s)) a)
  have hh := abs_integral_le_integral_abs (f := fun s =>
    LocalProfiles.bits G.book (G.snap (v,s)) a-
      (LocalProfiles.signed G.book (G.snap (v,s)) a.2.1-
        LocalProfiles.signed G.book (G.snap (v,s)) a.2.2))
    (μ := volume.restrict (Icc (-radius K G.support v) (radius K G.support v)))
  have hr₁ := threshold_in_range K h₁ v
  have hr₂ := threshold_in_range K h₂ v
  have ht : (∫s in Icc (-radius K G.support v) (radius K G.support v),
      LocalProfiles.bits G.book (G.snap (v,s)) a)=G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1 := by
    simp_rw [G.bits_eq]
    exact ThresholdProfiles.signed_bit_sub_integral hr₁.1 hr₁.2 hr₂.1 hr₂.2
  have ie := integral_sub hi (h₁i.sub h₂i)
  have ie' := integral_sub h₁i h₂i
  simp only [Pi.sub_apply] at ie ie'
  rw [ie,ie',ht] at hh
  exact hh.trans h

theorem size (a : Q×(P×P)) (v : Place K G.support)
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    G.heightAt a.2.1 v+G.heightAt a.2.2 v-G.errorAt false a v ≤
      |G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1| := by
  have hi := G.piece (fun d => LocalProfiles.bits G.book d a) v
  have h₁i := G.piece (fun d => LocalProfiles.X G.book d a.2.1) v
  have h₂i := G.piece (fun d => LocalProfiles.X G.book d a.2.2) v
  have he := G.piece (fun d => LocalProfiles.error2 G.book d a) v
  have h := integral_mono ((h₁i.add h₂i).sub he) hi.abs
    (fun s => LocalProfiles.size G.book (G.snap (v,s)) a)
  have ie := integral_sub (h₁i.add h₂i) he
  have ie' := integral_add h₁i h₂i
  simp only [Pi.sub_apply,Pi.add_apply] at h ie ie'
  rw [ie,ie'] at h
  have hr₁ := threshold_in_range K h₁ v
  have hr₂ := threshold_in_range K h₂ v
  have ht : (∫s in Icc (-radius K G.support v) (radius K G.support v),
      |LocalProfiles.bits G.book (G.snap (v,s)) a|)=|G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1| := by
    simp_rw [G.bits_eq]
    exact ThresholdProfiles.bit_sub_integral hr₁.1 hr₁.2 hr₂.1 hr₂.2
  rw [ht] at h
  exact h
end Input
end
end PlanarUnitDistances.ActualProfiles

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ProfileBudget
open MeasureTheory Set Finset FiniteLaw FiniteLawIntegral FiniteStarCoupling LevelSnapshot
  ScoreBook ActualScoreBook PlaceLevels ActualProfiles
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)

lemma weighted_nonneg {f : Place K G.support → ℝ} (hf : ∀v,0≤f v) : 0 ≤ weighted G f :=
  mul_nonneg (NNReal.coe_nonneg _) (sum_nonneg fun v _ => hf v)
lemma weighted_mono {f g : Place K G.support → ℝ} (hf : ∀v,f v≤g v) : weighted G f ≤ weighted G g :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => hf v) (NNReal.coe_nonneg _)
lemma weighted_add (f g : Place K G.support → ℝ) : weighted G (fun v => f v+g v)=weighted G f+weighted G g := by
  simp only [weighted,sum_add_distrib,mul_add]
lemma weighted_sub (f g : Place K G.support → ℝ) : weighted G (fun v => f v-g v)=weighted G f-weighted G g := by
  simp only [weighted,sum_sub_distrib,mul_sub]

lemma height_nonneg (p : P) : 0 ≤ height G p := weighted_nonneg G (G.height_nonneg p)
lemma error_nonneg (i : Bool) (a : Q×(P×P)) : 0 ≤ error G i a := weighted_nonneg G (G.error_nonneg i a)

theorem residual (a : Q×(P×P))
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-
      (G.profile a.2.1 v-G.profile a.2.2 v)) ≤ error G true a :=
  weighted_mono G (fun v => G.residual a v h₁ h₂)

theorem size (a : Q×(P×P))
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    height G a.2.1+height G a.2.2-error G false a ≤
      l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1) := by
  have h := weighted_mono G (fun v => G.size a v h₁ h₂)
  rw [weighted_sub,weighted_add] at h
  exact h
end
end PlanarUnitDistances.ProfileBudget

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Circles
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PopularCircles
open Finset UnitCodegree
open scoped Classical BigOperators
noncomputable section

lemma mem_neighbors {S : Finset ℂ} {p q : ℂ} : p∈neighbors S q ↔ p∈S ∧ dist p q=1 := mem_filter

lemma mem_candidates {S : Finset ℂ} {q : ℂ} (hq : 2≤(neighbors S q).card) : q∈candidates S := by
  obtain ⟨p,hp,r,hr,hpr⟩ := one_lt_card.mp (by omega : 1<(neighbors S q).card)
  have hp' := mem_neighbors.mp hp
  have hr' := mem_neighbors.mp hr
  apply mem_biUnion.mpr
  refine ⟨p,hp'.1,mem_biUnion.mpr ⟨r,hr'.1,?_⟩⟩
  simp only [hpr,↓reduceIte,Multiset.mem_toFinset]
  exact (Polynomial.mem_roots (centerPolynomial_ne_zero p r hpr)).mpr
    (centerPolynomial_eval p r q (unit_distance_equation p q hp'.2) (unit_distance_equation r q hr'.2))

theorem mem_popular {S : Finset ℂ} {q : ℂ} {k : ℕ} (hk : 2≤k) :
    q∈popular S k ↔ k≤(neighbors S q).card := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨mem_candidates (hk.trans h),h⟩

lemma intersection_card (S : Finset ℂ) {q r : ℂ} (hqr : q≠r) :
    ((neighbors S q).filter (fun p => dist p r=1)).card≤2 := by
  apply unit_centers_card q r hqr
  intro p hp
  have hh := mem_filter.mp hp
  exact ⟨by simpa only [dist_comm] using (mem_neighbors.mp hh.1).2,
    by simpa only [dist_comm] using hh.2⟩

lemma pair_neighbors (S : Finset ℂ) (q : ℂ) :
    S.offDiag.bipartiteAbove (fun (q : ℂ) (pr : ℂ × ℂ) => dist pr.1 q=1 ∧ dist pr.2 q=1) q=
      (neighbors S q).offDiag := by
  ext pr
  simp only [mem_bipartiteAbove,mem_offDiag,mem_neighbors]
  tauto

theorem count (S C : Finset ℂ) {k : ℕ}
    (hk : ∀q∈C,k≤(neighbors S q).card) :
    C.card*(k*(k-1))≤2*S.card^2 := by
  have h := card_nsmul_le_card_nsmul
    (r := fun (q : ℂ) (pr : ℂ × ℂ) => dist pr.1 q=1 ∧ dist pr.2 q=1)
    (s := C) (t := S.offDiag) (m := k*(k-1)) (n := (2:ℕ))
    (fun q hq => by
      rw [pair_neighbors,offDiag_card]
      change k*(k-1)≤(neighbors S q).card*(neighbors S q).card-(neighbors S q).card
      rw [show (neighbors S q).card*(neighbors S q).card-(neighbors S q).card=
        (neighbors S q).card*((neighbors S q).card-1) by rw [Nat.mul_sub_left_distrib,Nat.mul_one]]
      exact Nat.mul_le_mul (hk q hq) (Nat.sub_le_sub_right (hk q hq) 1))
    (fun pr hpr => by
      apply unit_centers_card pr.1 pr.2 (mem_offDiag.mp hpr).2.2
      intro q hq
      exact ((mem_bipartiteBelow _).mp hq).2)
  simp only [nsmul_eq_mul,offDiag_card] at h
  calc
    _ ≤ (S.card*S.card-S.card)*2 := h
    _ ≤ 2*S.card^2 := by nlinarith [Nat.sub_le (S.card*S.card) S.card]

lemma multi_pairs (C : Finset ℂ) (p : ℂ) :
    C.offDiag.bipartiteAbove (fun (p : ℂ) (qr : ℂ × ℂ) => dist p qr.1=1 ∧ dist p qr.2=1) p=
      (C.filter (fun q => dist p q=1)).offDiag := by
  ext qr
  simp only [mem_bipartiteAbove,mem_offDiag,mem_filter]
  tauto

theorem multiple_count (S C : Finset ℂ) : (multiple S C).card≤C.card^2 := by
  have h := card_nsmul_le_card_nsmul
    (r := fun (p : ℂ) (qr : ℂ × ℂ) => dist p qr.1=1 ∧ dist p qr.2=1)
    (s := multiple S C) (t := C.offDiag) (m := 2) (n := (2:ℕ))
    (fun p hp => by
      rw [multi_pairs,offDiag_card]
      have hh := (mem_filter.mp hp).2
      nlinarith [Nat.sub_add_cancel (show (C.filter (fun q => dist p q=1)).card≤
        (C.filter (fun q => dist p q=1)).card*(C.filter (fun q => dist p q=1)).card by nlinarith)])
    (fun qr hqr => by
      apply unit_centers_card qr.1 qr.2 (mem_offDiag.mp hqr).2.2
      intro p hp
      obtain ⟨_,h₁,h₂⟩ := (mem_bipartiteBelow _).mp hp
      exact ⟨by simpa only [dist_comm] using h₁,by simpa only [dist_comm] using h₂⟩)
  simp only [nsmul_eq_mul,offDiag_card] at h
  nlinarith [Nat.sub_le (C.card*C.card) C.card]

theorem exceptional_partner_count (S C : Finset ℂ) {p q : ℂ}
    (hp : p∈S) (hpm : p∉multiple S C) (hq : q∉C) :
    ((neighbors S q).filter (fun r => ∃c∈C,dist p c=1 ∧ dist r c=1)).card≤2 := by
  have hcard : (C.filter (fun c => dist p c=1)).card≤1 := by
    have hh : ¬2≤(C.filter (fun c => dist p c=1)).card := fun h => hpm (mem_filter.mpr ⟨hp,h⟩)
    omega
  by_cases he : ∃c∈C,dist p c=1
  · obtain ⟨c,hc,hpc⟩ := he
    have hu : ∀c'∈C,dist p c'=1 → c'=c := by
      intro c' hc' hpc'
      exact card_le_one.mp hcard c' (mem_filter.mpr ⟨hc',hpc'⟩) c (mem_filter.mpr ⟨hc,hpc⟩)
    have hsub : (neighbors S q).filter (fun r => ∃c∈C,dist p c=1 ∧ dist r c=1) ⊆
        (neighbors S q).filter (fun r => dist r c=1) := by
      intro r hr
      obtain ⟨hr,c',hc',hpc',hrc'⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr,by simpa [hu c' hc' hpc'] using hrc'⟩
    exact (card_le_card hsub).trans (intersection_card S (fun h => hq (h ▸ hc)))
  · have hz : (neighbors S q).filter (fun r => ∃c∈C,dist p c=1 ∧ dist r c=1)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro r _ ⟨c,hc,hpc,_⟩
      exact he ⟨c,hc,hpc⟩
    simp only [hz,card_empty]
    omega
end
end PlanarUnitDistances.PopularCircles

namespace PlanarUnitDistances.PopularCircleCost
open Finset FiniteLaw FiniteStarCoupling PopularCircles
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma event_injective_bound {X Y : Type*} [Fintype X] (μ : Law X) (f : X → Y)
    (hf : Function.Injective f) (S : Finset Y) {d : ℝ} (hd : 0 ≤ d)
    (hμ : ∀x,μ.val x ≤ d) : event μ (fun x => f x∈S) ≤ (S.card:ℝ)*d := by
  classical
  let A := univ.filter (fun x => f x∈S)
  have hcard : A.card ≤ S.card := by
    rw [←card_image_of_injective A hf]
    exact card_le_card (by intro y hy; obtain ⟨x,hx,rfl⟩ := mem_image.mp hy; exact (mem_filter.mp hx).2)
  calc
    _ = ∑x∈A,μ.val x := by
      simp only [A,sum_filter,event_eq_sum]
      apply sum_congr rfl
      intro x _
      split_ifs <;> rfl
    _ ≤ ∑x∈A,d := by apply sum_le_sum; exact fun x _ => hμ x
    _ = (A.card:ℝ)*d := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hd

lemma support_event_bound {X Y : Type*} [Fintype X] (μ : Law X) (f : X → Y)
    (hf : Function.Injective f) (S : Finset Y) (A : X → Prop)
    {d : ℝ} (hd : 0 ≤ d) (hμ : ∀x,μ.val x ≤ d)
    (hs : ∀x,0<μ.val x → A x → f x∈S) : event μ A ≤ (S.card:ℝ)*d := by
  have h : event μ A=event μ (fun x => A x ∧ f x∈S) := by
    unfold event avg
    apply sum_congr rfl
    intro x _
    by_cases hx : 0<μ.val x
    · by_cases ha : A x
      · simp [ha,hs x hx ha]
      · simp [ha]
    · have hz := le_antisymm (le_of_not_gt hx) (μ.nonneg x)
      simp [hz]
  rw [h]
  exact (event_mono μ (fun _ h => h.2)).trans (event_injective_bound μ f hf S hd hμ)

theorem cost (π : Law (P×Q)) (x : P → ℂ) (y : Q → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (S C : Finset ℂ) (hS : ∀p,x p∈S)
    (hu : ∀q p,0<(col π q).val p → dist (x p) (y q)=1)
    {μmax κmax d : ℝ} (hμ0 : 0 ≤ μmax) (hκ0 : 0 ≤ κmax) (hd0 : 0 ≤ d)
    (hμ : ∀p,(left π).val p ≤ μmax) (hκ : ∀q,(right π).val q ≤ κmax)
    (hd : ∀q p,(col π q).val p ≤ d) :
    event (WedgeLaw.law π) (fun a => ∃c∈C,dist (x a.2.1) c=1 ∧ dist (x a.2.2) c=1) ≤
      2*(C.card:ℝ)^2*μmax+(C.card:ℝ)*κmax+2*d := by
  let bad : P → P → Prop := fun p r => ∃c∈C,dist (x p) c=1 ∧ dist (x r) c=1
  let mult : P → Prop := fun p => x p∈multiple S C
  let cent : Q → Prop := fun q => y q∈C
  let residual : Q×(P×P) → Prop := fun a => ¬mult a.2.1 ∧ ¬cent a.1 ∧ bad a.2.1 a.2.2
  have hfirst : event (WedgeLaw.law π) (fun a => mult a.2.1) ≤ (C.card:ℝ)^2*μmax := by
    have he : event (WedgeLaw.law π) (fun a => mult a.2.1)=event (left π) mult :=
      by
        rw [←avg_ite (WedgeLaw.law π) (fun a => mult a.2.1),←avg_ite (left π) mult]
        exact WedgeLaw.first_point π (fun p => if mult p then 1 else 0)
    rw [he]
    calc
      _ ≤ ((multiple S C).card:ℝ)*μmax := event_injective_bound (left π) x hx _ hμ0 hμ
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast multiple_count S C) hμ0
  have hcenter : event (WedgeLaw.law π) (fun a => cent a.1) ≤ (C.card:ℝ)*κmax := by
    have he : event (WedgeLaw.law π) (fun a => cent a.1)=event (right π) cent := by
      unfold event
      rw [WedgeLaw.average]
      apply congrArg (avg (right π))
      funext q
      by_cases hc : cent q
      · simp only [hc,↓reduceIte,avg_const]
      · simp only [hc,↓reduceIte,avg_const]
    rw [he]
    exact event_injective_bound (right π) y hy C hκ0 hκ
  have hres : event (WedgeLaw.law π) residual ≤ 2*d := by
    unfold event
    rw [WedgeLaw.average]
    calc
      _ ≤ avg (right π) (fun _ => 2*d) := by
        apply avg_mono
        intro q
        rw [pair_avg]
        calc
          _ ≤ avg (col π q) (fun _ => 2*d) := by
            apply avg_mono
            intro p
            by_cases hp : mult p
            · simp only [residual,hp,not_true_eq_false,false_and,↓reduceIte,avg_const]
              positivity
            by_cases hq : cent q
            · simp only [residual,hq,not_true_eq_false,and_false,false_and,↓reduceIte,avg_const]
              positivity
            simp only [residual,hp,hq,not_false_eq_true,true_and]
            rw [avg_ite]
            let B := (neighbors S (y q)).filter (fun r => ∃c∈C,dist (x p) c=1 ∧ dist r c=1)
            have hc : B.card ≤ 2 := exceptional_partner_count S C (hS p) hp hq
            calc
              _ ≤ (B.card:ℝ)*d := support_event_bound (col π q) x hx B (bad p) hd0 (hd q)
                (fun r hr hbr => mem_filter.mpr ⟨mem_neighbors.mpr ⟨hS r,hu q r hr⟩,hbr⟩)
              _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) hd0
          _ = _ := avg_const _ _
      _ = _ := avg_const _ _
  have hcover : event (WedgeLaw.law π) (fun a => bad a.2.1 a.2.2) ≤
      event (WedgeLaw.law π) (fun a => mult a.2.1)+
      event (WedgeLaw.law π) (fun a => cent a.1)+event (WedgeLaw.law π) residual := by
    calc
      _ ≤ event (WedgeLaw.law π) (fun a => (mult a.2.1 ∨ cent a.1) ∨ residual a) := by
        apply event_mono
        intro a ha
        by_cases hp : mult a.2.1
        · exact Or.inl (Or.inl hp)
        by_cases hq : cent a.1
        · exact Or.inl (Or.inr hq)
        exact Or.inr ⟨hp,hq,ha⟩
      _ ≤ _ := (event_union_le _ _ _).trans (add_le_add (event_union_le _ _ _) le_rfl)
  have hn : 0 ≤ (C.card:ℝ)^2*μmax := by positivity
  change event (WedgeLaw.law π) (fun a => bad a.2.1 a.2.2) ≤ _
  linarith
end
end PlanarUnitDistances.PopularCircleCost

namespace PlanarUnitDistances.IncidencePopular
open Filter Finset FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale PowerGrowth
open scoped Classical
noncomputable section
variable (s : Sequence)
lemma points_card (i : ℕ) : (points s i).card=(s.P i).card :=
  card_image_of_injective _ UnitCodegree.zCoordinate.injective
lemma tpos (i : ℕ) : 0<s.t i := by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]
lemma center_atom (i : ℕ) (q : s.Q i) :
    (right (graph s i)).val q ≤ s.t i^(-1/2:ℝ) := by
  have hp : 0<((s.P i).card:ℝ) := Nat.cast_pos.mpr (GeometricLaw.card_pos _ _ (s.good i).positive).1
  have he := (s.good i).positive
  have hdp := (s.good i).degreeP
  have hm := (le_div_iff₀ hp).mp hdp
  have hpow := Real.rpow_pos_of_pos (tpos s i) (1/2:ℝ)
  rw [graph,GeometricLaw.right_eq]
  calc
    _ ≤ ((s.P i).card:ℝ)/CircleIncidence.incidences (s.P i) (s.Q i) :=
      div_le_div_of_nonneg_right (show CircleIncidence.degree (s.P i) q ≤ ((s.P i).card:ℝ) from by
        unfold CircleIncidence.degree
        exact_mod_cast Finset.card_filter_le (s.P i) _) he.le
    _ ≤ (27/50:ℝ)/(s.t i^(1/2:ℝ)) := by
      apply (div_le_div_iff₀ he hpow).mpr
      nlinarith
    _ ≤ 1/(s.t i^(1/2:ℝ)) := div_le_div_of_nonneg_right (by norm_num) hpow.le
    _ = s.t i^(-1/2:ℝ) := by rw [one_div,←Real.rpow_neg (tpos s i).le]; congr 1; norm_num
lemma column_atom (i : ℕ) (q : s.Q i) (p : s.P i) :
    (col (graph s i) q).val p ≤ 1/((i:ℝ)+1) := by
  have hp := (s.good i).center_degree_pos q
  have he := (s.good i).positive
  have hb := (le_div_iff₀ he).mp ((s.good i).atomQ q q.property)
  have hd : (i:ℝ)+1 ≤ CircleIncidence.degree (s.P i) q :=
    (s.good i).degreeQ.trans (by simpa only [div_mul_eq_mul_div] using hb)
  rw [graph,GeometricLaw.graph,UniformGraphLaw.col_eq _ _ (by rw [GeometricLaw.degree_eq]; exact hp),GeometricLaw.degree_eq]
  apply le_trans (div_le_div_of_nonneg_right (b:=(1:ℝ)) ?_ hp.le)
  · exact one_div_le_one_div_of_le (by positivity) hd
  · unfold IncidenceEntropy.indicator
    split_ifs <;> norm_num
lemma k_large : ∀ᶠi in atTop,2≤k s i := by
  filter_upwards [((tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/10)).comp s.tendsto).eventually_ge_atTop 2] with i hi
  have hh := hi.trans (Nat.le_ceil (s.t i^(9/10:ℝ)))
  exact_mod_cast hh
lemma count_bound : ∀ᶠi in atTop,(centers s i).card≤ s.t i^(6/25:ℝ) := by
  have hc := s.cardP_power.power_bound (by norm_num : (1:ℝ)<101/100)
  have hfort := eventually_constant_le_rpow s.tendsto (by norm_num : (0:ℝ)<1/50) 4
  filter_upwards [k_large s,hc,hfort] with i hk hc hfort
  have hcount := PopularCircles.count (points s i) (centers s i)
    (fun q hq => (PopularCircles.mem_popular hk).mp hq)
  have hk1 : 1≤k s i := by omega
  have hkr : (2:ℝ)≤k s i := by exact_mod_cast hk
  have hh : (centers s i).card*((k s i:ℝ)*((k s i:ℝ)-1))≤2*((s.P i).card:ℝ)^2 := by
    rw [points_card] at hcount
    exact_mod_cast hcount
  have hk0 := Nat.le_ceil (s.t i^(9/10:ℝ))
  have hpos := Real.rpow_pos_of_pos (tpos s i) (9/10:ℝ)
  have hcc : 0≤((centers s i).card:ℝ) := Nat.cast_nonneg _
  have hsquare : (s.t i^(9/10:ℝ))^2≤(k s i:ℝ)^2  := by gcongr; exact hk0
  have hc' : ((s.P i).card:ℝ)^2≤(s.t i^(101/100:ℝ))^2 := by gcongr
  have hbound : ((centers s i).card:ℝ)*(s.t i^(9/10:ℝ))^2 ≤ 4*(s.t i^(101/100:ℝ))^2 := by
    have hm := mul_le_mul_of_nonneg_left hsquare hcc
    nlinarith [mul_nonneg hcc (show 0≤(k s i:ℝ)*((k s i:ℝ)-2) by positivity)]
  have hp2 : (s.t i^(9/10:ℝ))^2=s.t i^(9/5:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul (tpos s i).le]; norm_num
  have hp3 : (s.t i^(101/100:ℝ))^2=s.t i^(101/50:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul (tpos s i).le]; norm_num
  rw [hp2,hp3] at hbound
  have hb : ((centers s i).card:ℝ)≤4*s.t i^(11/50:ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos (tpos s i) (9/5:ℝ))).mp
    calc
      _ ≤ 4*s.t i^(101/50:ℝ) := hbound
      _ = _ := by rw [mul_assoc,←Real.rpow_add (tpos s i)]; norm_num
  calc
    _ ≤ 4*s.t i^(11/50:ℝ) := hb
    _ ≤ s.t i^(1/50:ℝ)*s.t i^(11/50:ℝ) := mul_le_mul_of_nonneg_right hfort (Real.rpow_nonneg (tpos s i).le _)
    _ = _ := by rw [←Real.rpow_add (tpos s i)]; norm_num
lemma cost (i : ℕ) : event (WedgeLaw.law (graph s i)) (bad s i)≤
    2*((centers s i).card:ℝ)^2*s.t i^(-1/2:ℝ)+((centers s i).card:ℝ)*s.t i^(-1/2:ℝ)+2/((i:ℝ)+1) := by
  apply (PopularCircleCost.cost (graph s i) (fun p => UnitCodegree.zCoordinate p.val)
    (fun q => UnitCodegree.zCoordinate q.val)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (points s i) (centers s i) (fun p => mem_image.mpr ⟨p.val,p.property,rfl⟩)
    (fun q p h => ?_) (Real.rpow_nonneg (tpos s i).le _) (Real.rpow_nonneg (tpos s i).le _)
    (by positivity) (point_bound s i) (center_atom s i) (column_atom s i)).trans_eq
  · ring
  · rw [UnitCodegree.zCoordinate.dist_map]
    have hπ : 0<(graph s i).val (p,q) := by
      rw [←col_weight]
      exact mul_pos (positiveQ s i q) h
    exact IncidenceScale.support s i p q hπ
lemma cost_limit : Tendsto (fun i => event (WedgeLaw.law (graph s i)) (bad s i)) atTop (nhds 0) := by
  have h₁ : Tendsto (fun i => s.t i^(-1/50:ℝ)) atTop (nhds 0) :=
    by simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/50)).comp s.tendsto
  have h₂ : Tendsto (fun i => s.t i^(-13/50:ℝ)) atTop (nhds 0) :=
    by simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<13/50)).comp s.tendsto
  have hlim : Tendsto (fun i => 2*s.t i^(-1/50:ℝ)+s.t i^(-13/50:ℝ)+2/((i:ℝ)+1)) atTop (nhds 0) := by
    convert ((h₁.const_mul 2).add h₂).add (Sequence.accuracy_limit.const_mul 2) using 1 <;> simp [div_eq_mul_inv]
  apply squeeze_zero' (Eventually.of_forall (fun i => event_nonneg _ _)) _ hlim
  filter_upwards [count_bound s] with i hi
  calc
    _ ≤ _ := cost s i
    _ ≤ 2*(s.t i^(6/25:ℝ))^2*s.t i^(-1/2:ℝ)+s.t i^(6/25:ℝ)*s.t i^(-1/2:ℝ)+2/((i:ℝ)+1) := by
      have ht := tpos s i
      gcongr
    _ = _ := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (tpos s i).le,mul_assoc,←Real.rpow_add (tpos s i),←Real.rpow_add (tpos s i)]
      norm_num
end
end PlanarUnitDistances.IncidencePopular

namespace PlanarUnitDistances.LawDeletion
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {X P Q : Type*} [Fintype X] [Fintype P] [Fintype Q]
lemma cost (μ : Law X) (A B : X → Prop) :
    event μ A≤event μ (keep μ A B)+event μ B := by
  unfold event
  rw [←avg_add]
  apply FiniteLawIntegral.avg_mono_support
  intro x hx
  by_cases ha : A x <;> by_cases hb : B x <;> simp [keep,hx,ha,hb]
lemma wedge_support (π : Law (P×Q)) (a : Q×(P×P)) (ha : 0<(WedgeLaw.law π).val a) :
    0<π.val (a.2.1,a.1) ∧ 0<π.val (a.2.2,a.1) := by
  change 0<(right π).val a.1*((col π a.1).val a.2.1*(col π a.1).val a.2.2) at ha
  have hq : 0<(right π).val a.1 := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) ((right π).nonneg a.1)
    simp [hz] at ha
  have hpair := (mul_pos_iff_of_pos_left hq).mp ha
  have hp : 0<(col π a.1).val a.2.1 := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) ((col π a.1).nonneg a.2.1)
    simp [hz] at hpair
  have hr : 0<(col π a.1).val a.2.2 := (mul_pos_iff_of_pos_left hp).mp hpair
  constructor <;> rw [←col_weight]
  · exact mul_pos hq hp
  · exact mul_pos hq hr
end
end PlanarUnitDistances.LawDeletion

namespace PlanarUnitDistances.PlaceLogGeometry
open Finset PlaceLevels WeightedAbsoluteValues
open scoped BigOperators Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

lemma supported_of_mem {S : Finset K} {x : K} (hx : x∈S) : supported S x :=
  fun _ hv => log_off_support K hx hv

omit [NumberField K] in
lemma log_mul (v : AbsoluteValue K ℝ) {x y : K} (hx : x≠0) (hy : y≠0) :
    Real.log (v (x*y))=Real.log (v x)+Real.log (v y) := by
  rw [map_mul,Real.log_mul (v.pos hx).ne' (v.pos hy).ne']
omit [NumberField K] in
lemma log_div (v : AbsoluteValue K ℝ) {x y : K} (hx : x≠0) (hy : y≠0) :
    Real.log (v (x/y))=Real.log (v x)-Real.log (v y) := by
  rw [map_div₀,Real.log_div (v.pos hx).ne' (v.pos hy).ne']
lemma supported_mul {S : Finset K} {x y : K} (hx : x≠0) (hy : y≠0)
    (hsx : supported S x) (hsy : supported S y) : supported S (x*y) := by
  intro v hv
  rw [log_mul _ hx hy,hsx v hv,hsy v hv,add_zero]
lemma supported_div {S : Finset K} {x y : K} (hx : x≠0) (hy : y≠0)
    (hsx : supported S x) (hsy : supported S y) : supported S (x/y) := by
  intro v hv
  rw [log_div _ hx hy,hsx v hv,hsy v hv,sub_self]

lemma height_identity [IsGalois ℚ K] (S : Finset K) {x : K} (hx : x≠0) (hs : supported S x) :
    (LevelScale.weight K:ℝ)*(∑v : Place K S,|Real.log (av K v x)|)=2*exactHeight K x := by
  have hf : (∑v : ↥(finiteSupport K S),|Real.log (finiteEntry K v.val.1 v.val.2 x)|)=
      ∑ᶠv : Nat.Primes×Gal(K/ℚ),|Real.log (finiteEntry K v.1 v.2 x)| := by
    rw [Finset.sum_coe_sort (finiteSupport K S) (fun v => |Real.log (finiteEntry K v.1 v.2 x)|)]
    symm
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hn
    apply hv
    simp only [hs v hn,abs_zero]
  rw [Fintype.sum_sum_type]
  change (Module.finrank ℚ K:ℝ)⁻¹*((∑σ : K →ₐ[ℚ] ℂ,|Real.log (infiniteEntry K σ x)|)+
    (∑v : ↥(finiteSupport K S),|Real.log (finiteEntry K v.val.1 v.val.2 x)|))=_
  rw [hf,mul_comm,←div_eq_mul_inv]
  exact weighted_abs_log_eq_twice K hx

omit [NumberField K] in
lemma unit_pair_identity {d d' e e' : K} (hd : d≠0) (hd' : d'≠0)
    (he : d*e=1) (he' : d'*e'=1) :
    (d-d')*(e-e')=2-d/d'-(d/d')⁻¹ := by
  have h₁ : e=1/d := (eq_div_iff hd).mpr (by simpa only [mul_comm] using he)
  have h₂ : e'=1/d' := (eq_div_iff hd').mpr (by simpa only [mul_comm] using he')
  rw [h₁,h₂]
  field_simp
  ring

theorem rectangle [IsGalois ℚ K] (S : Finset K) (a b c d : K)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0)
    (hsa : supported S a) (hsb : supported S b) (hsc : supported S c) (hsd : supported S d)
    (f f' g g' : Place K S → ℝ) {E₁ E₂ E₃ E₄ : ℝ}
    (h₁ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v a)+f v-g v|)≤E₁)
    (h₂ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v b)+f' v-g' v|)≤E₂)
    (h₃ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v c)+f v-g' v|)≤E₃)
    (h₄ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v d)+f' v-g v|)≤E₄) :
    2*exactHeight K (a*b/(c*d))≤E₁+E₂+E₃+E₄ := by
  have hx := div_ne_zero (mul_ne_zero ha hb) (mul_ne_zero hc hd)
  have hs := supported_div (mul_ne_zero ha hb) (mul_ne_zero hc hd)
    (supported_mul ha hb hsa hsb) (supported_mul hc hd hsc hsd)
  rw [←height_identity S hx hs]
  have hh : ∀v : Place K S,|Real.log (av K v (a*b/(c*d)))|≤
      |Real.log (av K v a)+f v-g v|+|Real.log (av K v b)+f' v-g' v|+
      |Real.log (av K v c)+f v-g' v|+|Real.log (av K v d)+f' v-g v| := by
    intro v
    rw [log_div _ (mul_ne_zero ha hb) (mul_ne_zero hc hd),log_mul _ ha hb,log_mul _ hc hd]
    have he : Real.log (av K v a)+Real.log (av K v b)-(Real.log (av K v c)+Real.log (av K v d))=
        (Real.log (av K v a)+f v-g v)+(Real.log (av K v b)+f' v-g' v)-
        (Real.log (av K v c)+f v-g' v)-(Real.log (av K v d)+f' v-g v) := by ring
    rw [he]
    have h₁ := abs_sub
      ((Real.log (av K v a)+f v-g v)+(Real.log (av K v b)+f' v-g' v)-(Real.log (av K v c)+f v-g' v))
      (Real.log (av K v d)+f' v-g v)
    have h₂ := abs_sub
      ((Real.log (av K v a)+f v-g v)+(Real.log (av K v b)+f' v-g' v))
      (Real.log (av K v c)+f v-g' v)
    have h₃ := abs_add_le (Real.log (av K v a)+f v-g v) (Real.log (av K v b)+f' v-g' v)
    linarith

  have h := mul_le_mul_of_nonneg_left (sum_le_sum (s := univ) (fun v _ => hh v))
    (NNReal.coe_nonneg (LevelScale.weight K))
  simp only [sum_add_distrib,mul_add] at h
  linarith
end
end PlanarUnitDistances.PlaceLogGeometry

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Extraction
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.OrganizedProfiles
open Finset PlaceLevels WeightedAbsoluteValues ActualProfiles ProfileBudget PlaceLogGeometry
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)

theorem log_ratio (a : Q×(P×P)) (v : Place K G.support)
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0) :
    Real.log (av K v (ratio G a))= -(G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1) := by
  rw [ratio,PlaceLogGeometry.log_div _ h₁ h₂]
  unfold Input.threshold jump
  ring

lemma ratio_supported (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support) :
    supported G.support (ratio G a) :=
  supported_div h₁ h₂ (supported_of_mem hs₁) (supported_of_mem hs₂)

lemma log_residual (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support) :
    l1 G (fun v => Real.log (av K v (ratio G a))+G.profile a.2.1 v-G.profile a.2.2 v)≤error G true a := by
  have he : l1 G (fun v => Real.log (av K v (ratio G a))+G.profile a.2.1 v-G.profile a.2.2 v)=
      l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-(G.profile a.2.1 v-G.profile a.2.2 v)) := by
    unfold l1 weighted
    congr 1
    apply sum_congr rfl
    intro v _
    dsimp only
    rw [log_ratio G a v h₁ h₂]
    convert abs_neg (G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-(G.profile a.2.1 v-G.profile a.2.2 v)) using 1; congr 1; ring
  rw [he]
  exact ProfileBudget.residual G a hs₁ hs₂

lemma height_lower [IsGalois ℚ K] (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support) :
    height G a.2.1+height G a.2.2-error G false a≤2*exactHeight K (ratio G a) := by
  rw [←height_identity G.support (show ratio G a≠0 from div_ne_zero h₁ h₂) (ratio_supported G a h₁ h₂ hs₁ hs₂)]
  have he : (LevelScale.weight K:ℝ)*(∑v : Place K G.support,|Real.log (av K v (ratio G a))|)=
      l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1) := by
    unfold l1 weighted
    congr 1
    apply sum_congr rfl
    intro v _
    dsimp only
    rw [log_ratio G a v h₁ h₂,abs_neg]
  rw [he]
  exact ProfileBudget.size G a hs₁ hs₂

theorem selected [IsGalois ℚ K] (a : Q×(P×P)) {J δ : ℝ}
    (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support)
    (hband : J≤height G a.2.1+height G a.2.2 ∧ height G a.2.1+height G a.2.2≤2*J)
    (herr : error G true a+error G false a≤δ*(height G a.2.1+height G a.2.2)) :
    a.2.1≠a.2.2 ∧ J/3≤exactHeight K (ratio G a) ∧
      l1 G (fun v => Real.log (av K v (ratio G a))+G.profile a.2.1 v-G.profile a.2.2 v)≤2*δ*J := by
  have e₁ := error_nonneg G true a
  have e₂ := error_nonneg G false a
  have hlow := height_lower G a h₁ h₂ hs₁ hs₂
  have hw := add_nonneg (height_nonneg G a.2.1) (height_nonneg G a.2.2)
  have hh : J/3≤exactHeight K (ratio G a) := by
    nlinarith [mul_le_mul_of_nonneg_right hδ' hw]
  refine ⟨?_,hh,?_⟩
  · intro he
    have hz : ratio G a=1 := by unfold ratio; rw [he,div_self h₂]
    rw [hz,exactHeight_one] at hh
    linarith
  · have hr := log_residual G a h₁ h₂ hs₁ hs₂
    nlinarith [mul_le_mul_of_nonneg_left hband.2 hδ]

theorem identity (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1*(G.w (G.point a.2.1)-G.w (G.center a.1))=1)
    (h₂ : jump G a.2.2 a.1*(G.w (G.point a.2.2)-G.w (G.center a.1))=1) :
    (G.z (G.point a.2.1)-G.z (G.point a.2.2))*(G.w (G.point a.2.1)-G.w (G.point a.2.2))=
      2-ratio G a-(ratio G a)⁻¹ := by
  have hn₁ : jump G a.2.1 a.1≠0 := by intro hz; simp [hz] at h₁
  have hn₂ : jump G a.2.2 a.1≠0 := by intro hz; simp [hz] at h₂
  calc
    _ = (jump G a.2.1 a.1-jump G a.2.2 a.1)*
        ((G.w (G.point a.2.1)-G.w (G.center a.1))-(G.w (G.point a.2.2)-G.w (G.center a.1))) := by
      unfold jump
      ring
    _ = _ := PlaceLogGeometry.unit_pair_identity hn₁ hn₂ h₁ h₂
end
end PlanarUnitDistances.OrganizedProfiles

namespace PlanarUnitDistances.OrganizedGraph
open Finset PlaceLevels WeightedAbsoluteValues ActualProfiles ProfileBudget PlaceLogGeometry OrganizedProfiles
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H) (A : Q×(P×P) → Prop)

omit [IsGalois ℚ K] in
lemma label_eq {p r : P} (h : edge A p r) :
    label G A p r=ratio G (h.choose,(p,r)) := dite_eq_left h

theorem properties {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (hs : ∀a,A a → jump G a.2.1 a.1∈G.support ∧ jump G a.2.2 a.1∈G.support)
    (hu : ∀a,A a →
      jump G a.2.1 a.1*(G.w (G.point a.2.1)-G.w (G.center a.1))=1 ∧
      jump G a.2.2 a.1*(G.w (G.point a.2.2)-G.w (G.center a.1))=1)
    (hband : ∀a,A a → J≤height G a.2.1+height G a.2.2 ∧ height G a.2.1+height G a.2.2≤2*J)
    (herr : ∀a,A a → error G true a+error G false a≤δ*(height G a.2.1+height G a.2.2)) :
    (∀p r,edge A p r → p≠r ∧ label G A p r≠0 ∧ J/3≤exactHeight K (label G A p r) ∧
      (G.z (G.point p)-G.z (G.point r))*(G.w (G.point p)-G.w (G.point r))=
        2-label G A p r-(label G A p r)⁻¹) ∧
    (∀p p' r r',edge A p r → edge A p r' → edge A p' r → edge A p' r' →
      exactHeight K (label G A p r*label G A p' r'/(label G A p r'*label G A p' r))≤4*δ*J) := by
  have hns (a) (ha : A a) : jump G a.2.1 a.1≠0 ∧ jump G a.2.2 a.1≠0 :=
    ⟨left_ne_zero_of_mul_eq_one (hu a ha).1,left_ne_zero_of_mul_eq_one (hu a ha).2⟩
  have hE (a) (ha : A a) := selected G a hJ hδ hδ' (hns a ha).1 (hns a ha).2
    (hs a ha).1 (hs a ha).2 (hband a ha) (herr a ha)
  have hl (p r) (h : edge A p r) : label G A p r≠0 ∧ supported G.support (label G A p r) ∧
      l1 G (fun v => Real.log (av K v (label G A p r))+G.profile p v-G.profile r v)≤2*δ*J := by
    rw [label_eq G A h]
    exact ⟨div_ne_zero (hns _ h.choose_spec).1 (hns _ h.choose_spec).2,
      ratio_supported G _ (hns _ h.choose_spec).1 (hns _ h.choose_spec).2
        (hs _ h.choose_spec).1 (hs _ h.choose_spec).2,(hE _ h.choose_spec).2.2⟩
  constructor
  · intro p r h
    refine ⟨(hE _ h.choose_spec).1,(hl p r h).1,?_,?_⟩
    · rw [label_eq G A h]
      exact (hE _ h.choose_spec).2.1
    · rw [label_eq G A h]
      exact identity G _ (hu _ h.choose_spec).1 (hu _ h.choose_spec).2
  · intro p p' r r' h₁ h₂ h₃ h₄
    have hb := PlaceLogGeometry.rectangle G.support
      (label G A p r) (label G A p' r') (label G A p r') (label G A p' r)
      (hl p r h₁).1 (hl p' r' h₄).1 (hl p r' h₂).1 (hl p' r h₃).1
      (hl p r h₁).2.1 (hl p' r' h₄).2.1 (hl p r' h₂).2.1 (hl p' r h₃).2.1
      (G.profile p) (G.profile p') (G.profile r) (G.profile r')
      (hl p r h₁).2.2 (hl p' r' h₄).2.2 (hl p r' h₂).2.2 (hl p' r h₃).2.2
    linarith
end
end PlanarUnitDistances.OrganizedGraph

namespace PlanarUnitDistances.IncidenceSelected
open Filter Finset FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceHeights OrganizedProfiles WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}

local instance instFintypeSumSubtypePlaneMemFinsetPQ_r63dbe4_1 : Fintype (s.P i⊕s.Q i) := inferInstance
local instance instFintypeProdSubtypePlaneMemFinsetPQ_r63dbe4_1 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
lemma properties (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3) :
    (∀p r,edge R J δ p r → p≠r ∧ label R J δ p r≠0 ∧ J/3≤exactHeight (model s i).field (label R J δ p r) ∧
      ((model s i).z (.inl p)-(model s i).z (.inl r))*((model s i).w (.inl p)-(model s i).w (.inl r))=
      2-label R J δ p r-(label R J δ p r)⁻¹) ∧
    (∀p p' r r',edge R J δ p r → edge R J δ p r' → edge R J δ p' r → edge R J δ p' r' →
      exactHeight (model s i).field (label R J δ p r*label R J δ p' r'/(label R J δ p r'*label R J δ p' r))≤4*δ*J) := by
  apply OrganizedGraph.properties R.input (kept R J δ) hJ hδ hδ'
  · intro x _
    exact ⟨(model s i).sub_mem (.inl x.2.1) (.inr x.1),(model s i).sub_mem (.inl x.2.2) (.inr x.1)⟩
  · intro x hx
    have hh := LawDeletion.wedge_support (graph s i) x hx.1
    exact ⟨(model s i).unit_identity _ _ (support s i _ _ hh.1),
      (model s i).unit_identity _ _ (support s i _ _ hh.2)⟩
  · intro x hx
    exact ⟨hx.2.1.1,hx.2.1.2.1⟩
  · intro x hx
    exact hx.2.1.2.2

lemma no_popular (R : Realization s a i) {J δ : ℝ} (p r : s.P i) (he : edge R J δ p r) :
    ∀c∈IncidencePopular.centers s i,¬(dist (UnitCodegree.zCoordinate p.val) c=1 ∧
      dist (UnitCodegree.zCoordinate r.val) c=1) := by
  obtain ⟨q,hq⟩ := he
  intro c hc h
  exact hq.2.2 ⟨c,hc,h.1,h.2⟩

lemma count (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3) :
    event (WedgeLaw.law (graph s i)) (kept R J δ) *
      (CircleIncidence.incidences (s.P i) (s.Q i)*((27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card)/2) ≤ (pairs R J δ).card := by
  have he := (s.good i).positive
  have hc : 0<((s.Q i).card:ℝ) := Nat.cast_pos.mpr (GeometricLaw.card_pos _ _ he).2
  have hd : 0<(27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card := by positivity
  have hdeg (q : s.Q i) : (27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card≤
      IncidenceEntropy.degree (GeometricLaw.E (s.P i) (s.Q i)) q := by
    rw [GeometricLaw.degree_eq]
    have hh := (le_div_iff₀ he).mp ((s.good i).atomQ q q.property)
    simpa only [div_mul_eq_mul_div] using hh
  have hcodeg := IncidenceEntropy.unit_incidence_codegree (GeometricLaw.E (s.P i) (s.Q i))
    (fun p => UnitCodegree.zCoordinate p.val) (fun q => UnitCodegree.zCoordinate q.val)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (fun p q h => by rw [UnitCodegree.zCoordinate.dist_map]; exact h)
  have hb := UniformGraphLaw.edge_count (GeometricLaw.E (s.P i) (s.Q i))
    (by rw [GeometricLaw.edgeCount_eq]; exact he) hd hdeg hcodeg (kept R J δ)
    (fun x hx => (properties R hJ hδ hδ').1 x.2.1 x.2.2 ⟨x.1,hx⟩ |>.1)
  have hb' : event (WedgeLaw.law (graph s i)) (kept R J δ)≤
    ((pairs R J δ).card:ℝ)*2/(IncidenceEntropy.edgeCount (GeometricLaw.E (s.P i) (s.Q i))*((27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card)) := by
    convert hb using 1
    all_goals simp only [graph,GeometricLaw.graph,pairs,edge,OrganizedGraph.edge,Prod.eta]
    all_goals congr 8
  rw [GeometricLaw.edgeCount_eq] at hb'
  have hh := (le_div_iff₀ (mul_pos he hd)).mp hb'
  nlinarith

theorem choose (s : Sequence) : ∃c : ℝ,0<c ∧ ∀δ : ℝ,0<δ → δ≤1/3 →
    ∃a : BudgetParameters.Params,∃b : ℝ,0<b ∧ ∀ᶠi in atTop,∃R : Realization s a i,∃J : ℝ,
      0<J ∧ c*scale s i/2≤J ∧
      b*(CircleIncidence.incidences (s.P i) (s.Q i)*((27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card)/2)≤(pairs R J δ).card := by
  obtain ⟨c,hc,h⟩ := IncidenceBand.choose s
  refine ⟨c,hc,?_⟩
  intro δ hδ hδ'
  obtain ⟨a,b,hb,h⟩ := h δ hδ
  refine ⟨a,b/2,by positivity,?_⟩
  filter_upwards [h,(IncidencePopular.cost_limit s).eventually_le_const (by positivity : 0<b/2),
    (scale_limit s).eventually_gt_atTop 0] with i hi hcost hscale
  obtain ⟨R,J,hJ,hband⟩ := hi
  have hJ0 : 0<J := lt_of_lt_of_le (by positivity) hJ
  refine ⟨R,J,hJ0,hJ,?_⟩
  have hkeep := LawDeletion.cost (WedgeLaw.law (graph s i)) (IncidenceBand.band R J δ) (IncidencePopular.bad s i)
  change event (WedgeLaw.law (graph s i)) (IncidenceBand.band R J δ)≤
    event (WedgeLaw.law (graph s i)) (kept R J δ)+event (WedgeLaw.law (graph s i)) (IncidencePopular.bad s i) at hkeep
  have hp : b/2≤event (WedgeLaw.law (graph s i)) (kept R J δ) := by linarith
  have he := (s.good i).positive
  exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans (count R hJ0 hδ.le hδ')
end
end PlanarUnitDistances.IncidenceSelected

namespace PlanarUnitDistances.ImageRelation
open Finset
open scoped Classical
noncomputable section
variable {α β K : Type*}
variable (P : Finset α) (f : α → β) (hf : Function.Injective f)
lemma inv_val (p : image P f) : f ((equiv P f hf).symm p)=p :=
  congrArg Subtype.val ((equiv P f hf).apply_symm_apply p)
variable (E : P → P → Prop) (l : P → P → K) [One K]
lemma edge_iff (p r : image P f) : edge P f hf E p r ↔
    E ((equiv P f hf).symm p) ((equiv P f hf).symm r) := by
  constructor
  · rintro ⟨hp,hr,h⟩; exact h
  · intro h; exact ⟨p.property,r.property,h⟩
lemma label_eq (p r : image P f) : label P f hf l p r=
    l ((equiv P f hf).symm p) ((equiv P f hf).symm r) := by
  simp only [label,p.property,r.property,↓reduceDIte]
lemma card : (univ.filter (fun pr : image P f×image P f => edge P f hf E pr.1 pr.2)).card=
    (univ.filter (fun pr : P×P => E pr.1 pr.2)).card := by
  apply card_bij (fun pr _ => ((equiv P f hf).symm pr.1,(equiv P f hf).symm pr.2))
  · intro pr hpr
    exact mem_filter.mpr ⟨mem_univ _,(edge_iff P f hf E _ _).mp (mem_filter.mp hpr).2⟩
  · intro pr _ qr _ h
    apply Prod.ext
    · exact (equiv P f hf).symm.injective (congrArg Prod.fst h)
    · exact (equiv P f hf).symm.injective (congrArg Prod.snd h)
  · intro pr hpr
    refine ⟨(equiv P f hf pr.1,equiv P f hf pr.2),?_,?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _,(edge_iff P f hf E _ _).mpr ?_⟩
      simpa only [Equiv.symm_apply_apply] using (mem_filter.mp hpr).2
    · simp
end
end PlanarUnitDistances.ImageRelation

namespace PlanarUnitDistances.IncidenceComplex
open Finset IncidenceSequence IncidenceScale IncidenceBook IncidenceSelected
open scoped Classical
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
lemma pull_coord (p : IncidencePopular.points s i) : UnitCodegree.zCoordinate (pull p).val=p :=
  ImageRelation.inv_val _ _ _ p

lemma edge_iff (R : Realization s a i) (J δ : ℝ) (p r : IncidencePopular.points s i) :
    edge R J δ p r ↔ IncidenceSelected.edge R J δ (pull p) (pull r) := ImageRelation.edge_iff _ _ _ _ p r
lemma label_eq (R : Realization s a i) (J δ : ℝ) (p r : IncidencePopular.points s i) :
    label R J δ p r=IncidenceSelected.label R J δ (pull p) (pull r) := ImageRelation.label_eq _ _ _ _ p r
lemma card (R : Realization s a i) (J δ : ℝ) :
    (univ.filter (fun pr : IncidencePopular.points s i×IncidencePopular.points s i => edge R J δ pr.1 pr.2)).card=
    (pairs R J δ).card := ImageRelation.card _ _ _ _
lemma z_pull (p : IncidencePopular.points s i) : ((model s i).z (.inl (pull p)):ℂ)=p := by
  rw [(model s i).z_eq]
  exact pull_coord p
lemma w_pull (p : IncidencePopular.points s i) : ((model s i).w (.inl (pull p)):ℂ)=star p.val := by
  rw [(model s i).w_eq]
  exact congrArg star (pull_coord p)
lemma nonzero (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) : label R J δ p r≠0 := by
  rw [label_eq]
  exact (IncidenceSelected.properties R hJ hδ hδ').1 _ _ ((edge_iff R J δ p r).mp he) |>.2.1
lemma large (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) :
    J/3≤WeightedAbsoluteValues.exactHeight (model s i).field (label R J δ p r) := by
  rw [label_eq]
  exact (IncidenceSelected.properties R hJ hδ hδ').1 _ _ ((edge_iff R J δ p r).mp he) |>.2.2.1
lemma distance (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) :
    (p.val-r.val)*(star p.val-star r.val)=2-(label R J δ p r:ℂ)-(label R J δ p r:ℂ)⁻¹ := by
  have h := (IncidenceSelected.properties R hJ hδ hδ').1 _ _ ((edge_iff R J δ p r).mp he) |>.2.2.2
  have hh := congrArg (model s i).field.val h
  simp only [map_mul,map_sub,map_ofNat,map_inv₀] at hh
  simpa only [IntermediateField.coe_val,←label_eq R J δ p r,z_pull,w_pull] using hh
lemma rectangle (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p p' r r' : IncidencePopular.points s i) (h₁ : edge R J δ p r) (h₂ : edge R J δ p r')
    (h₃ : edge R J δ p' r) (h₄ : edge R J δ p' r') :
    WeightedAbsoluteValues.exactHeight (model s i).field
      (label R J δ p r*label R J δ p' r'/(label R J δ p r'*label R J δ p' r))≤4*δ*J := by
  simp only [label_eq]
  exact (IncidenceSelected.properties R hJ hδ hδ').2 _ _ _ _
    ((edge_iff R J δ p r).mp h₁) ((edge_iff R J δ p r').mp h₂)
    ((edge_iff R J δ p' r).mp h₃) ((edge_iff R J δ p' r').mp h₄)
lemma no_circle (R : Realization s a i) {J δ : ℝ} (hk : 2≤IncidencePopular.k s i)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) (c : ℂ)
    (hc : s.t i^(9/10:ℝ)≤((IncidencePopular.points s i).filter (fun v => ‖v-c‖=1)).card) :
    ¬(‖p.val-c‖=1 ∧ ‖r.val-c‖=1) := by
  have hcount : IncidencePopular.k s i≤(PopularCircles.neighbors (IncidencePopular.points s i) c).card := by
    apply Nat.ceil_le.mpr
    simpa only [PopularCircles.neighbors,dist_eq_norm] using hc
  have hh := IncidenceSelected.no_popular R (pull p) (pull r) ((edge_iff R J δ p r).mp he)
    c ((PopularCircles.mem_popular hk).mpr hcount)
  simpa only [pull_coord,dist_eq_norm] using hh
end
end PlanarUnitDistances.IncidenceComplex

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UnitDistances.UltraField
open Filter

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i, Field (K i)]

noncomputable instance instIsAlgClosedFieldProduct [∀ i, IsAlgClosed (K i)] : IsAlgClosed (FieldProduct U K) := by
  classical
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (mk U K)
    Ideal.Quotient.mk_surjective p
  have hn : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)
  have hc : mk U K (q.coeff p.natDegree) ≠ 0 := by
    rw [← Polynomial.coeff_map, hq, Polynomial.coeff_natDegree, hp.leadingCoeff]
    exact one_ne_zero
  have hev : ∀ᶠ i in U, q.coeff p.natDegree i ≠ 0 :=
    Ultrafilter.eventually_not.mpr ((mk_eq_zero U K _).not.mp hc)
  have hroot : ∀ᶠ i in U, ∃ x : K i,
      (q.map (Pi.evalRingHom K i)).IsRoot x := by
    filter_upwards [hev] with i hi
    apply IsAlgClosed.exists_root
    have hb : (p.natDegree : WithBot ℕ) ≤ (q.map (Pi.evalRingHom K i)).degree := by
      apply Polynomial.le_degree_of_ne_zero
      simpa using hi
    have hz : (0 : WithBot ℕ) < p.natDegree := by exact_mod_cast hn
    exact ne_of_gt (lt_of_lt_of_le hz hb)
  let r : ∀ i, K i := fun i => if h : ∃ x : K i,
      (q.map (Pi.evalRingHom K i)).IsRoot x then Classical.choose h else 0
  refine ⟨mk U K r, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  apply (mk_eq_zero U K _).mpr
  filter_upwards [hroot] with i hi
  have hr : (q.map (Pi.evalRingHom K i)).eval (r i) = 0 := by
    dsimp only [r]
    rw [dite_eq_left hi]
    exact Classical.choose_spec hi
  rw [Polynomial.eval_map] at hr
  change (Pi.evalRingHom K i) (q.eval r) = 0
  rw [← Polynomial.eval₂_at_apply]
  exact hr

end UnitDistances.UltraField

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceDiagonal
open Filter Finset IncidenceSequence IncidenceScale IncidenceBook PowerGrowth
open scoped Classical
noncomputable section

lemma delta_pos (n : ℕ) : 0<delta n := by unfold delta; positivity
lemma delta_le (n : ℕ) : delta n≤1/3 := by
  unfold delta
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]
lemma delta_limit : Tendsto delta atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1/(3*((n:ℝ)+1))) atTop (nhds 0)
  convert Sequence.accuracy_limit.div_const 3 using 1 <;> simp [div_eq_mul_inv,mul_comm]

theorem exists_data (s : Sequence) : Nonempty (Data s) := by
  obtain ⟨c,hc,h⟩ := IncidenceSelected.choose s
  choose a b hb h using fun n => h (delta n) (delta_pos n) (delta_le n)
  have hh (n : ℕ) : ∀ᶠi in atTop,∃R : Realization s (a n) i,∃J : ℝ,
      0<J ∧ (n:ℝ)+1≤J ∧
      s.t i^(2-1/((n:ℝ)+1))≤(IncidenceSelected.pairs R J (delta n)).card ∧
      2≤IncidencePopular.k s i := by
    filter_upwards [h n,(s.wedge_power.const_mul s.tendsto (hb n)) (1/((n:ℝ)+1)) (by positivity),
      (scale_limit s).eventually_ge_atTop (2*((n:ℝ)+1)/c),IncidencePopular.k_large s] with i hi hpow hscale hk
    obtain ⟨R,J,hJ,hJ',hcount⟩ := hi
    have hc' := (div_le_iff₀ hc).mp hscale
    exact ⟨R,J,hJ,by nlinarith,hpow.trans hcount,hk⟩
  obtain ⟨f,hf,h⟩ := PowerGrowth.diagonal hh
  choose R J hJ hj hd hk using h
  exact ⟨⟨f,hf,a,R,J,hJ,hj,hd,hk⟩⟩

namespace Data
variable {s : Sequence} (D : Data s)
lemma t_limit : Tendsto D.t atTop atTop := s.tendsto.comp D.cofinal
lemma J_limit : Tendsto D.J atTop atTop :=
  tendsto_atTop_mono (fun n => (by linarith [D.large n] : (n:ℝ)≤D.J n)) tendsto_natCast_atTop_atTop
lemma card_power : Upper atTop D.t (fun n => ((D.P n).card:ℝ)) 1 := by
  intro ε hε
  filter_upwards [D.cofinal.eventually (s.cardP_power ε hε)] with n hn
  simpa only [P,t,IncidencePopular.points_card] using hn
lemma edge_power : Lower atTop D.t
    (fun n => (GenericGrid.edges (fun n (p r : D.P n) => D.E n p r) n).card) 2 := by
  intro ε hε
  filter_upwards [Sequence.accuracy_limit.eventually_le_const hε] with n hn
  have ht : 1 ≤ s.t (D.f n) := by linarith [s.large (D.f n),Nat.cast_nonneg (α:=ℝ) (D.f n)]
  have h := (Real.rpow_le_rpow_of_exponent_le ht (by linarith : 2-ε≤2-1/((n:ℝ)+1))).trans (D.dense n)
  rw [←IncidenceComplex.card (D.R n) (D.J n) (delta n)] at h
  dsimp only [GenericGrid.edges,E,P,t]
  convert h using 1
  all_goals congr 8
lemma residual_small : (fun n => 4*delta n*D.J n)=o[atTop] D.J := by
  apply (Asymptotics.isLittleO_iff_tendsto (fun n h => (D.positive n).ne' h |>.elim)).mpr
  have h := delta_limit.const_mul 4
  convert h using 1
  · ext n
    exact mul_div_cancel_right₀ (4*delta n) (D.positive n).ne'
  · simp
end Data
end
end PlanarUnitDistances.IncidenceDiagonal

namespace PlanarUnitDistances.IncidenceDiagonal
open Filter PowerGrowth IncidenceSequence
open scoped Classical
noncomputable section
namespace Data
variable {s : Sequence} (D : Data s)
lemma hypotheses (U : Ultrafilter ℕ) (hU : (U:Filter ℕ)≤atTop) :
    AlgebraicObstruction.Hypotheses U D.t D.J D.P D.E D.K D.e D.ell := by
  constructor
  · intro n p hp r hr he
    exact IncidenceComplex.nonzero (D.R n) (D.positive n) (delta_pos n).le (delta_le n)
      ⟨p,hp⟩ ⟨r,hr⟩ he
  · intro n p hp r hr he
    exact IncidenceComplex.distance (D.R n) (D.positive n) (delta_pos n).le (delta_le n)
      ⟨p,hp⟩ ⟨r,hr⟩ he
  · refine ⟨1/3,by norm_num,?_⟩
    intro n p hp r hr he
    have hh := IncidenceComplex.large (D.R n) (D.positive n) (delta_pos n).le (delta_le n) ⟨p,hp⟩ ⟨r,hr⟩ he
    change (1/3)*D.J n≤WeightedAbsoluteValues.exactHeight (IncidenceScale.model s (D.f n)).field
      (IncidenceComplex.label (D.R n) (D.J n) (delta n) p r)
    convert hh using 1 <;> first | rfl | ring
  · refine ⟨fun n => 4*delta n*D.J n,D.residual_small.mono hU,?_⟩
    intro n p hp p' hp' r hr r' hr' h₁ h₂ h₃ h₄
    exact IncidenceComplex.rectangle (D.R n) (D.positive n) (delta_pos n).le (delta_le n)
      ⟨p,hp⟩ ⟨p',hp'⟩ ⟨r,hr⟩ ⟨r',hr'⟩ h₁ h₂ h₃ h₄
  · intro n p hp r hr he c hc
    exact IncidenceComplex.no_circle (D.R n) (D.popular n) ⟨p,hp⟩ ⟨r,hr⟩ he c hc

end Data

theorem impossible (s : Sequence) : False := by
  obtain ⟨D⟩ := exists_data s
  let U := Filter.hyperfilter ℕ
  have hU : (U:Filter ℕ)≤atTop := Nat.hyperfilter_le_atTop
  exact AlgebraicObstruction.no_rectangles U hU D.t D.J (D.t_limit.mono_left hU)
    (D.J_limit.mono_left hU) D.P (fun ε hε => hU (D.card_power ε hε))
    D.E (fun ε hε => hU (D.edge_power ε hε)) D.K D.e D.ell (D.hypotheses U hU)
end
end PlanarUnitDistances.IncidenceDiagonal

namespace PlanarUnitDistances
open Filter PowerGrowth

theorem main_oai : ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < (4 : ℝ) / 3 ∧
    ∀ n : ℕ, (u n : ℝ) ≤ C * (n : ℝ) ^ β := by
  by_contra h
  obtain ⟨t,X,ht,ht1,hX0,_,hX,hE,hAlg⟩ := counterexample_power_sequence h
  obtain ⟨s⟩ := IncidenceSequence.diagonal_sequence ht ht1 hX0 hX hE hAlg
  exact IncidenceDiagonal.impossible s
end PlanarUnitDistances

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.main_oai := @OAI.PlanarUnitDistances.main_oai
