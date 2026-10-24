-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.HasBorderDeterminant.smooth_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:56:52.258583+00:00
-- url     : https://prove2.me/submissions/cd83663c-9560-4b7d-be56-3596a3da5727

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_OAIQWPB000

section
-- module Solutions.OAIQW_PermanentBorder.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Multigraded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma project_mul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (g : MvPolynomial σ K) (d : G) :
    weightedHomogeneousComponent w d (a * g) =
      a * weightedHomogeneousComponent w (d-e) g := by
  classical
  ext z
  simp only [coeff_weightedHomogeneousComponent, coeff_mul]
  have hi : (if Finsupp.weight w z = d then
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z, a.coeff xy.1 * g.coeff xy.2 else 0) =
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z,
        if Finsupp.weight w z = d then a.coeff xy.1 * g.coeff xy.2 else 0 := by
    rw [Finset.sum_ite_irrel]
    simp
  rw [hi]
  apply Finset.sum_congr rfl
  rintro ⟨x,y⟩ hxy
  have hsum : x+y=z := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
  by_cases hx : a.coeff x = 0
  · simp [hx]
  · have hwe : Finsupp.weight w x = e := ha hx
    have hcond : Finsupp.weight w z = d ↔ Finsupp.weight w y = d-e := by
      rw [← hsum, map_add, hwe]
      rw [eq_sub_iff_add_eq, add_comm]
    simp only [hcond]
    split_ifs <;> simp

lemma componentClosed_sup {I J : Ideal (MvPolynomial σ K)}
    (hI : ComponentClosed w I) (hJ : ComponentClosed w J) :
    ComponentClosed w (I ⊔ J) := by
  intro p hp d
  obtain ⟨i,hi,j,hj,rfl⟩ := Submodule.mem_sup.mp hp
  rw [map_add]
  exact Ideal.add_mem _ (Submodule.mem_sup_left (hI i hi d))
    (Submodule.mem_sup_right (hJ j hj d))

lemma componentClosed_span_single {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) :
    ComponentClosed w (Ideal.span {a}) := by
  intro p hp d
  obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hp
  rw [project_mul w ha]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a))

lemma componentClosed_bot : ComponentClosed (K := K) w ⊥ := by
  intro p hp d
  have hp0 : p = 0 := hp
  simp [hp0]

theorem finrank_product_split (I : Ideal (MvPolynomial σ K))
    (hI : ComponentClosed w I) {a b : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G)
    [Module.Finite K (Piece (K := K) w d)]
    [Module.Finite K (Piece (K := K) w (d-e))] :
    Module.finrank K (componentQuotient w (I ⊔ Ideal.span {a*b}) d) ≤
      Module.finrank K (componentQuotient w (I ⊔ Ideal.span {a}) d) +
      Module.finrank K (componentQuotient w (I ⊔ Ideal.span {b}) (d-e)) := by
  let B := I ⊔ Ideal.span {a*b}
  let A := I ⊔ Ideal.span {a}
  let C := I ⊔ Ideal.span {b}
  have hBA : B ≤ A := by
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hm : ∀ p ∈ C, a*p ∈ B := by
    intro p hp
    obtain ⟨i,hi,z,hz,rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hz
    rw [mul_add, ← mul_assoc]
    exact Ideal.add_mem _ (Submodule.mem_sup_left (I.mul_mem_left a hi))
      (Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  let f := componentMap w hBA d
  let g := componentMul w ha C B hm d
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro x hx
    obtain ⟨p,rfl⟩ := Submodule.mkQ_surjective _ x
    change (Submodule.Quotient.mk p : componentQuotient w A d) = 0 at hx
    have hp : p.val ∈ A := (Submodule.Quotient.mk_eq_zero
      ((A.restrictScalars K).comap (Piece (K := K) w d).subtype)).mp hx
    obtain ⟨i,hi,z,hz,hp⟩ := Submodule.mem_sup.mp hp
    obtain ⟨u,rfl⟩ := Ideal.mem_span_singleton.mp hz
    let v : Piece (K := K) w (d-e) :=
      ⟨weightedHomogeneousComponent w (d-e) u, weightedHomogeneousComponent_mem w u (d-e)⟩
    refine ⟨Submodule.Quotient.mk v, ?_⟩
    change Submodule.Quotient.mk (mulPiece w ha d v) = Submodule.Quotient.mk p
    rw [Submodule.Quotient.eq]
    change a * weightedHomogeneousComponent w (d-e) u - p.val ∈ B
    have he : weightedHomogeneousComponent w d i +
        a * weightedHomogeneousComponent w (d-e) u = p.val := by
      have hh := congrArg (weightedHomogeneousComponent w d) hp
      simpa only [map_add, project_mul w ha,
        weightedHomogeneousComponent_eq_self p.property] using hh
    have hi' := hI i hi d
    have he' : a * weightedHomogeneousComponent w (d-e) u - p.val =
        -(weightedHomogeneousComponent w d i) := by rw [← he]; abel
    rw [he']
    exact Submodule.mem_sup_left (I.neg_mem hi')
  have hk := (Submodule.finrank_mono hker).trans (LinearMap.finrank_range_le g)
  have hf := Submodule.finrank_le (LinearMap.range f)
  have hr := LinearMap.finrank_range_add_finrank_ker f
  dsimp only [B,A,C] at hk hf hr
  omega

lemma productIdeal_closed (qs : List (FactorPair (K := K) w)) :
    ComponentClosed w (productIdeal w qs) := by
  induction qs with
  | nil => exact componentClosed_bot w
  | cons q qs ih =>
    exact componentClosed_sup w
      (componentClosed_span_single w (q.left_homogeneous.mul q.right_homogeneous)) ih

theorem finrank_le_splitBound [∀ d, Module.Finite K (Piece (K := K) w d)]
    (qs : List (FactorPair (K := K) w)) (I : Ideal (MvPolynomial σ K))
    (hI : ComponentClosed w I) (d : G) :
    Module.finrank K (componentQuotient w (I ⊔ productIdeal w qs) d) ≤
      splitBound w I d qs := by
  induction qs generalizing I d with
  | nil => rw [productIdeal, sup_bot_eq, splitBound]
  | cons q qs ih =>
    have hs := finrank_product_split w (b := q.right) (I ⊔ productIdeal w qs)
      (componentClosed_sup w hI (productIdeal_closed w qs)) q.left_homogeneous d
    have h₁ := ih (I ⊔ Ideal.span {q.left})
      (componentClosed_sup w hI (componentClosed_span_single w q.left_homogeneous)) d
    have h₂ := ih (I ⊔ Ideal.span {q.right})
      (componentClosed_sup w hI (componentClosed_span_single w q.right_homogeneous))
      (d-q.leftDegree)
    calc
      _ ≤ Module.finrank K (componentQuotient w
            ((I ⊔ Ideal.span {q.left}) ⊔ productIdeal w qs) d) +
          Module.finrank K (componentQuotient w
            ((I ⊔ Ideal.span {q.right}) ⊔ productIdeal w qs) (d-q.leftDegree)) := by
        have h₀ : I ⊔ productIdeal w (q::qs) =
            (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.left*q.right} := by
          dsimp only [productIdeal]
          rw [sup_comm (Ideal.span {q.left*q.right}) (productIdeal w qs), ← sup_assoc]
        have hₐ : (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.left} =
            (I ⊔ Ideal.span {q.left}) ⊔ productIdeal w qs := sup_right_comm _ _ _
        have hᵦ : (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.right} =
            (I ⊔ Ideal.span {q.right}) ⊔ productIdeal w qs := sup_right_comm _ _ _
        rw [hₐ,hᵦ] at hs
        rw [h₀]
        exact hs
      _ ≤ _ := Nat.add_le_add h₁ h₂

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

lemma sum_blockWeight (group : σ → ι) (m : σ →₀ ℕ) :
    ∑ j, Finsupp.weight (blockWeight group) m j = (m.degree : ℤ) := by
  classical
  rw [Finsupp.weight_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_comm]
  simp only [blockWeight, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_eq_sum]
  simp

lemma finite_block_degree (group : σ → ι) (d : ι → ℤ) :
    Set.Finite {m : σ →₀ ℕ | Finsupp.weight (blockWeight group) m = d} := by
  apply (Finsupp.finite_of_degree_le (∑ j, d j).toNat).subset
  intro m hm
  have hs := sum_blockWeight group m
  rw [hm] at hs
  change m.degree ≤ (∑ j, d j).toNat
  rw [hs]
  simp

instance blockPiece_finite (group : σ → ι) (d : ι → ℤ) :
    Module.Finite K (Piece (K := K) (blockWeight group) d) := by
  rw [Piece, weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_block_degree group d).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K
    {m | Finsupp.weight (blockWeight group) m = d})

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma weight_blockExponent (group : σ → ι) (m : σ →₀ ℕ) (j : ι) :
    Finsupp.weight (blockWeight group) m j = (blockExponent group m j : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, blockWeight, nsmul_eq_mul]
  simp [blockExponent, Pi.single_apply, Finset.sum_filter, eq_comm]

lemma prod_blockExponent {S : Type*} [CommMonoid S] (group : σ → ι)
    (m : σ →₀ ℕ) (z : ι → S) :
    ∏ v, z (group v) ^ m v = ∏ j, z j ^ blockExponent group m j := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ group]
  apply Finset.prod_congr rfl
  intro j _
  rw [blockExponent, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

omit [Fintype σ] [Fintype ι] in
lemma componentEmbed_injective (group : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) : Function.Injective (componentEmbed group I d) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
    ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
  change Submodule.Quotient.mk p = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

theorem component_finrank_le_one_of_linear_relations (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (z : ι → MvPolynomial σ K) (c : σ → K)
    (hrel : ∀ v, X v - C (c v) * z (group v) ∈ I) (d : ι → ℤ) :
    Module.finrank K (componentQuotient (blockWeight group) I d) ≤ 1 := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let Z := ∏ j, q (z j) ^ (d j).toNat
  have hX (v : σ) : q (X v) = algebraMap K _ (c v) * q (z (group v)) := by
    have h := Ideal.Quotient.eq.mpr (hrel v)
    change q (X v) = q (C (c v) * z (group v)) at h
    rw [map_mul] at h
    exact h.trans (congrArg (· * q (z (group v))) (q.commutes (c v)))
  have hmon (m : σ →₀ ℕ) (r : K) (hm : Finsupp.weight (blockWeight group) m = d) :
      q (monomial m r) ∈ Submodule.span K {Z} := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r * ∏ v, c v ^ m v, ?_⟩
    have hexp : ∀ j, blockExponent group m j = (d j).toNat := by
      intro j
      have h := congrFun hm j
      rw [weight_blockExponent] at h
      rw [← h, Int.toNat_natCast]
    rw [monomial_eq, Finsupp.prod_pow, map_mul, map_prod]
    simp only [map_pow, hX, mul_pow, Finset.prod_mul_distrib]
    rw [prod_blockExponent group m (fun j => q (z j))]
    simp only [hexp]
    change (r * ∏ v, c v ^ m v) • Z =
      algebraMap K _ r * ((∏ v, (algebraMap K _ (c v)) ^ m v) * Z)
    have he : (r * ∏ v, c v ^ m v) • Z =
        algebraMap K (MvPolynomial σ K ⧸ I) (r * ∏ v, c v ^ m v) * Z :=
      Algebra.smul_def (R := K) (A := MvPolynomial σ K ⧸ I) (r * ∏ v, c v ^ m v) Z
    rw [he, map_mul, map_prod]
    simp only [map_pow]
    ring
  have hpiece (p : Piece (K := K) (blockWeight group) d) :
      q p.val ∈ Submodule.span K {Z} := by
    rcases p with ⟨p,hp⟩
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p₁ p₂ _ _ h₁ h₂ => simpa only [map_add] using Submodule.add_mem _ h₁ h₂
    | monomial m r hm => exact hmon m r hm
  let f := (componentEmbed group I d).codRestrict (Submodule.span K {Z}) (by
    intro x
    obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
      ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
    exact hpiece p)
  have hf : Function.Injective f := fun a b h =>
    componentEmbed_injective group I d (congrArg Subtype.val h)
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans
    (by
      apply finrank_le_one_iff.mpr
      refine ⟨⟨Z, Submodule.subset_span (Set.mem_singleton Z)⟩, ?_⟩
      intro x
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp x.property
      exact ⟨c, Subtype.ext hc⟩)

theorem component_finrank_zero_of_block_killed (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (j : ι)
    (hkill : ∀ v, group v = j → X v ∈ I) (d : ι → ℤ) (hd : 0 < d j) :
    Module.finrank K (componentQuotient (blockWeight group) I d) = 0 := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  have hmon (m : σ →₀ ℕ) (r : K) (hm : Finsupp.weight (blockWeight group) m = d) :
      q (monomial m r) = 0 := by
    have hexp : 0 < blockExponent group m j := by
      have h := congrFun hm j
      rw [weight_blockExponent] at h
      omega
    obtain ⟨v,hv,hmv⟩ := Finset.sum_pos_iff.mp hexp
    have hqv : q (X v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (hkill v (Finset.mem_filter.mp hv).2)
    rw [monomial_eq, Finsupp.prod_pow, map_mul, map_prod]
    have hz : ∏ v, q (X v ^ m v) = 0 := Finset.prod_eq_zero (Finset.mem_univ v) (by
      rw [map_pow, hqv, zero_pow (Nat.ne_of_gt hmv)])
    rw [hz, mul_zero]
  have hpiece (p : Piece (K := K) (blockWeight group) d) : q p.val = 0 := by
    rcases p with ⟨p,hp⟩
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => exact map_zero q
    | add p₁ p₂ _ _ h₁ h₂ => rw [map_add, h₁,h₂,add_zero]
    | monomial m r hm => exact hmon m r hm
  apply Module.finrank_eq_zero_iff.mpr
  intro x
  refine ⟨1,one_ne_zero,?_⟩
  rw [one_smul]
  apply componentEmbed_injective group I d
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
    ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
  rw [map_zero]
  exact hpiece p

end LinearLeaves
end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.LinearForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearCoefficients
variable {K σ τ : Type*} [Field K] [Fintype τ]

lemma linearFormMap_single [DecidableEq τ] (v : τ → σ) (t : τ) :
    linearFormMap v (Pi.single t (1 : K)) = X (v t) := by
  classical
  simp [linearFormMap_apply, Pi.single_apply]

theorem linear_relations_of_codimension_le_one (v : τ → σ) (I : Ideal (MvPolynomial σ K))
    (h : Module.finrank K ((τ → K) ⧸ linearCoefficientSubspace v I) ≤ 1) :
    ∃ z : MvPolynomial σ K, ∃ c : τ → K, ∀ t, X (v t) - C (c t) * z ∈ I := by
  classical
  obtain ⟨a,ha⟩ := finrank_le_one_iff.mp h
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective (linearCoefficientSubspace v I) a
  choose c hc using fun t => ha (Submodule.Quotient.mk (Pi.single t (1 : K)))
  refine ⟨linearFormMap v b,c,fun t => ?_⟩
  have hmem : Pi.single t (1 : K) - c t • b ∈ linearCoefficientSubspace v I := by
    apply (Submodule.Quotient.eq (linearCoefficientSubspace v I)).mp
    simpa only [Submodule.Quotient.mk_smul] using (hc t).symm
  change linearFormMap v (Pi.single t 1 - c t • b) ∈ I at hmem
  simpa only [map_sub, map_smul, linearFormMap_single, smul_eq_C_mul] using hmem

theorem variables_mem_of_codimension_zero (v : τ → σ) (I : Ideal (MvPolynomial σ K))
    (h : Module.finrank K ((τ → K) ⧸ linearCoefficientSubspace v I) = 0) :
    ∀ t, X (v t) ∈ I := by
  classical
  intro t
  have hz : Submodule.Quotient.mk (Pi.single t (1 : K)) =
      (0 : (τ → K) ⧸ linearCoefficientSubspace v I) := by
    obtain ⟨c,hc,hq⟩ := Module.finrank_eq_zero_iff.mp h
      (Submodule.Quotient.mk (Pi.single t (1 : K)))
    exact (smul_eq_zero.mp hq).resolve_left hc
  have hm := (Submodule.Quotient.mk_eq_zero (linearCoefficientSubspace v I)).mp hz
  change linearFormMap v (Pi.single t (1 : K)) ∈ I at hm
  simpa only [linearFormMap_single] using hm

end LinearCoefficients

section Vandermonde
variable {K : Type*} [Field K]

lemma linearIndependent_rect_vandermonde {n N : ℕ} (hn : n ≤ N)
    (t : Fin n → K) (ht : Function.Injective t) :
    LinearIndependent K (fun i : Fin n => fun j : Fin N => t i ^ j.val) := by
  let f : (Fin N → K) →ₗ[K] Fin n → K :=
    LinearMap.funLeft K K (Fin.castLE hn)
  apply LinearIndependent.of_comp f
  exact Matrix.linearIndependent_rows_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr ht)

lemma linear_block_codimension_le {σ : Type*} {n N : ℕ} (hn : n ≤ N)
    (v : Fin N → σ) (I : Ideal (MvPolynomial σ K))
    (t : Fin n → K) (ht : Function.Injective t)
    (hforms : ∀ i, linearFormMap v (fun j => t i ^ j.val) ∈ I) :
    Module.finrank K ((Fin N → K) ⧸ linearCoefficientSubspace v I) + n ≤ N := by
  have hi := linearIndependent_rect_vandermonde hn t ht
  have hspan : Submodule.span K (Set.range (fun i : Fin n => fun j : Fin N => t i ^ j.val)) ≤
      linearCoefficientSubspace v I := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hforms i
  have hr := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hi, Fintype.card_fin] at hr
  have he := Submodule.finrank_quotient_add_finrank (linearCoefficientSubspace v I)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  omega

end Vandermonde
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section VandermondeLeaves
variable {K ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype L]

omit [Fintype ι] in
lemma labeled_codimension (a : ι → ℕ) (g : L → ι) (t : L → K)
    (ht : Function.Injective t) (I : Ideal (MvPolynomial (BlockVariables a) K))
    (hforms : ∀ l, blockLinearForm a (g l) (t l) ∈ I)
    (j : ι) (n : ℕ) (hn : n ≤ a j+1) (hj : n ≤ Fintype.card {l // g l = j}) :
    Module.finrank K ((Fin (a j+1) → K) ⧸ linearCoefficientSubspace (blockVar a j) I) + n ≤ a j+1 := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin n)
    (β := {l // g l = j}) (by simpa using hj)
  apply linear_block_codimension_le hn (blockVar a j) I (fun i => t (e i).val)
    (ht.comp (Subtype.val_injective.comp e.injective))
  intro i
  have h := hforms (e i).val
  have hij : g (e i).val = j := (e i).property
  rw [hij] at h
  exact h

theorem labeled_leaf_bound (a : ι → ℕ) (g : L → ι) (t : L → K)
    (ht : Function.Injective t) (hcard : Fintype.card L = ∑ j, a j)
    (I : Ideal (MvPolynomial (BlockVariables a) K))
    (hforms : ∀ l, blockLinearForm a (g l) (t l) ∈ I)
    (d : ι → ℤ) (hd : ∀ j, 0 < d j) :
    Module.finrank K (componentQuotient (blockWeight (fun v : BlockVariables a => v.1)) I d) ≤
      if ∀ j, Fintype.card {l // g l = j} = a j then 1 else 0 := by
  classical
  split_ifs with hbalanced
  · have hj (j : ι) :
        Module.finrank K ((Fin (a j+1) → K) ⧸ linearCoefficientSubspace (blockVar a j) I) ≤ 1 := by
      have h := labeled_codimension a g t ht I hforms j (a j) (by omega) (by rw [hbalanced])
      omega
    choose z c hc using fun j => linear_relations_of_codimension_le_one (blockVar a j) I (hj j)
    exact component_finrank_le_one_of_linear_relations (fun v : BlockVariables a => v.1) I z
      (fun v => c v.1 v.2) (fun v => hc v.1 v.2) d
  · have hs : (∑ j, Fintype.card {l // g l = j}) = ∑ j, a j := by
      rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv g), hcard]
    have hex : ∃ j, a j < Fintype.card {l // g l = j} := by
      by_contra! hn
      apply hbalanced
      exact fun j => (Finset.sum_eq_sum_iff_of_le (fun j _ => hn j)).mp hs j (Finset.mem_univ j)
    obtain ⟨j,hj⟩ := hex
    have hdim := labeled_codimension a g t ht I hforms j (a j+1) le_rfl hj
    have hz := variables_mem_of_codimension_zero (blockVar a j) I (by omega)
    have hb : ∀ v : BlockVariables a, v.1 = j → X v ∈ I := by
      rintro ⟨i,v⟩ hv
      change i = j at hv
      subst i
      exact hz v
    exact (component_finrank_zero_of_block_killed (fun v : BlockVariables a => v.1) I j hb d (hd j)).le

end VandermondeLeaves
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BinaryChoices
variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma splitBound_eq_choiceSum (qs : List (FactorPair (K := K) w))
    (I : Ideal (MvPolynomial σ K)) (d : G) :
    splitBound w I d qs = ∑ c : Fin qs.length → Bool,
      pieceDim w (I ⊔ choiceIdeal w qs c) (d-choiceShift w qs c) := by
  classical
  induction qs generalizing I d with
  | nil =>
    change pieceDim w I d = ∑ c : Fin 0 → Bool,
      pieceDim w (I ⊔ choiceIdeal w [] c) (d-choiceShift w [] c)
    simp only [choiceIdeal, choiceShift, sup_bot_eq, sub_zero]
    simp
  | cons q qs ih =>
    rw [splitBound, ih, ih]
    let f : (Fin (qs.length+1) → Bool) → ℕ := fun c =>
      pieceDim w (I ⊔ choiceIdeal w (q::qs) c) (d-choiceShift w (q::qs) c)
    have hs := (Fin.consEquiv (fun _ : Fin (qs.length+1) => Bool)).sum_comp f
    apply Eq.trans (b := ∑ p : Bool × (Fin qs.length → Bool), f (Fin.cons p.1 p.2)) _ hs
    simp only [f, Fintype.sum_prod_type, Fintype.sum_bool,
      choiceIdeal, choiceShift, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true,
      ite_false, ite_true, zero_add, ← sup_assoc]
    simp_rw [sub_add_eq_sub_sub]
    exact add_comm _ _

lemma choice_mem_choiceIdeal (qs : List (FactorPair (K := K) w))
    (c : Fin qs.length → Bool) (i : Fin qs.length) :
    (if c i then (qs.get i).right else (qs.get i).left) ∈ choiceIdeal w qs c := by
  induction qs with
  | nil => exact Fin.elim0 i
  | cons q qs ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    · exact Submodule.mem_sup_right (ih (fun j => c j.succ) i)

end BinaryChoices
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section MixedCoefficient
variable {ι E : Type*} [Fintype E] [DecidableEq ι]

lemma choiceCount_apply (g : E → ι) (j : ι) :
    choiceCount g j = Fintype.card {e // g e = j} := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [choiceCount, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit [DecidableEq ι] in
lemma mixedPolynomial_eq_choices [DecidableEq E] (u v : E → ι) :
    mixedPolynomial u v = ∑ c : E → Bool,
      monomial (choiceCount (fun e => if c e then v e else u e)) (1 : ℕ) := by
  classical
  have h := Fintype.prod_sum (fun e (b : Bool) =>
    if b then X (v e) else X (u e) : E → Bool → MvPolynomial ι ℕ)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  rw [mixedPolynomial]
  simp_rw [add_comm] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  rw [choiceCount, monomial_sum_one]
  apply Finset.prod_congr rfl
  intro e _
  cases c e <;> rfl

lemma mixed_coefficient_eq_count [Fintype ι] [DecidableEq E] (u v : E → ι) (a : ι →₀ ℕ) :
    (mixedPolynomial u v).coeff a =
      ∑ c : E → Bool, if ∀ j,
        Fintype.card {e // (if c e then v e else u e) = j} = a j then 1 else 0 := by
  classical
  rw [mixedPolynomial_eq_choices, coeff_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [coeff_monomial]
  congr 1
  rw [Finsupp.ext_iff]
  simp only [choiceCount_apply]

end MixedCoefficient
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section ComparisonPieceBound
variable {K ι σ : Type*} [Field K] [DecidableEq ι]

omit [DecidableEq ι] in
lemma choiceShift_le_length (w : σ → (ι → ℤ))
    (qs : List (FactorPair (K := K) w)) (c : Fin qs.length → Bool)
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1) (j : ι) :
    choiceShift w qs c j ≤ (qs.length : ℤ) := by
  induction qs with
  | nil => simp [choiceShift]
  | cons q qs ih =>
    have hq := hdeg q (List.mem_cons_self) j
    have hs := ih (fun i => c i.succ) (fun q h => hdeg q (List.mem_cons_of_mem _ h))
    by_cases hc : c 0 = true
    · simpa [choiceShift, hc, add_comm] using add_le_add hq hs
    · simpa [choiceShift, hc] using hs.trans (show (qs.length : ℤ) ≤ qs.length + 1 by omega)

variable [Fintype ι]

theorem comparison_piece_bound (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := K) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → K)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j) (d : ι → ℤ) (hd : ∀ j, (qs.length : ℤ) < d j) :
    pieceDim (blockWeight (fun v : BlockVariables a => v.1))
      (productIdeal (blockWeight (fun v : BlockVariables a => v.1)) qs) d ≤
      (mixedPolynomial u v).coeff a := by
  classical
  let w := blockWeight (fun v : BlockVariables a => v.1)
  have hf := finrank_le_splitBound w qs ⊥ (componentClosed_bot w) d
  change pieceDim w (⊥ ⊔ productIdeal w qs) d ≤ splitBound w ⊥ d qs at hf
  rw [bot_sup_eq] at hf
  apply hf.trans
  rw [splitBound_eq_choiceSum, mixed_coefficient_eq_count]
  apply Finset.sum_le_sum
  intro c _
  simp only [bot_sup_eq]
  let g : Fin qs.length → ι := fun i => if c i then v i else u i
  let t' : Fin qs.length → K := fun i => t (i,c i)
  have ht' : Function.Injective t' := by
    intro i j hij
    exact congrArg Prod.fst (ht hij)
  have hforms (i : Fin qs.length) :
      blockLinearForm a (g i) (t' i) ∈ choiceIdeal w qs c := by
    have h := choice_mem_choiceIdeal w qs c i
    dsimp only [g,t']
    cases hc : c i
    · simpa only [hc, Bool.false_eq_true, ite_false, hleft i] using h
    · simpa only [hc, ite_true, hright i] using h
  have hp (j : ι) : 0 < (d-choiceShift w qs c) j := by
    have hb := choiceShift_le_length w qs c hdeg j
    have hh := hd j
    simp only [Pi.sub_apply]
    omega
  exact labeled_leaf_bound a g t' ht' (by simpa using hlen)
    (choiceIdeal w qs c) hforms (d-choiceShift w qs c) hp

end ComparisonPieceBound
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section HomogeneousIdealMap
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]
variable (w : σ → G) (e : E → G) (F : E → MvPolynomial σ K)
  (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))

lemma homogeneousIdealMap_val (d : G) (p : ∀ i : E, Piece (K := K) w (d-e i)) :
    (homogeneousIdealMap w e F hF d p).val = ∑ i, F i * (p i).val := by
  simp [homogeneousIdealMap]

lemma homogeneousIdealMap_range (d : G) :
    LinearMap.range (homogeneousIdealMap w e F hF d) =
      ((Ideal.span (Set.range F)).restrictScalars K).comap (Piece (K := K) w d).subtype := by
  classical
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    change (homogeneousIdealMap w e F hF d g).val ∈ Ideal.span (Set.range F)
    rw [homogeneousIdealMap_val]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_span_range_self)
  · intro hp
    change p.val ∈ Ideal.span (Set.range F) at hp
    obtain ⟨g,hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    let g' : ∀ i : E, Piece (K := K) w (d-e i) := fun i =>
      ⟨weightedHomogeneousComponent w (d-e i) (g i),
        weightedHomogeneousComponent_mem w (g i) (d-e i)⟩
    refine ⟨g', Subtype.ext ?_⟩
    rw [homogeneousIdealMap_val]
    change ∑ i, F i * weightedHomogeneousComponent w (d-e i) (g i) = p.val
    simp_rw [← project_mul w (hF _)]
    rw [← map_sum]
    simp_rw [mul_comm (F _) _]
    rw [hg, weightedHomogeneousComponent_eq_self p.property]

lemma homogeneousIdealMap_affine (Q : E → MvPolynomial σ K)
    (hQ : ∀ i, (Q i).IsWeightedHomogeneous w (e i)) (d : G) (t : K) :
    homogeneousIdealMap w e (fun i => (1-t) • Q i + t • F i)
      (fun i => (isWeightedHomogeneous_smul w (hQ i) (1-t)).add
        (isWeightedHomogeneous_smul w (hF i) t)) d =
      (1-t) • homogeneousIdealMap w e Q hQ d + t • homogeneousIdealMap w e F hF d := by
  classical
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
    Submodule.coe_smul]
  rw [homogeneousIdealMap_val, homogeneousIdealMap_val, homogeneousIdealMap_val]
  simp only [add_mul, smul_mul_assoc, Finset.sum_add_distrib, ← Finset.smul_sum]

end HomogeneousIdealMap

lemma pairProduct_mem_productIdeal {K σ G : Type*} [Field K] [AddCommGroup G]
    (w : σ → G) (qs : List (FactorPair (K := K) w)) (i : Fin qs.length) :
    (qs.get i).left * (qs.get i).right ∈ productIdeal w qs := by
  induction qs with
  | nil => exact Fin.elim0 i
  | cons q qs ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    · exact Submodule.mem_sup_right (ih i)

lemma productIdeal_le {K σ G : Type*} [Field K] [AddCommGroup G]
    (w : σ → G) (qs : List (FactorPair (K := K) w)) (I : Ideal (MvPolynomial σ K))
    (h : ∀ i : Fin qs.length, (qs.get i).left * (qs.get i).right ∈ I) :
    productIdeal w qs ≤ I := by
  induction qs with
  | nil => exact bot_le
  | cons q qs ih =>
    exact sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (h 0)))
      (ih (fun i => h i.succ))

lemma productIdeal_eq_span {K σ G : Type*} [Field K] [AddCommGroup G]
    (w : σ → G) (qs : List (FactorPair (K := K) w)) :
    productIdeal w qs = Ideal.span (Set.range (fun i : Fin qs.length =>
      (qs.get i).left * (qs.get i).right)) := by
  apply le_antisymm
  · exact productIdeal_le w qs _ (fun _ => Ideal.mem_span_range_self)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact pairProduct_mem_productIdeal w qs i

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
section AffineIndependent
variable {K E V : Type*} [Field K] [Fintype E]
  [AddCommGroup V] [Module K V]

theorem affine_independent_polynomial (v w : E → V) (hv : LinearIndependent K v) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      LinearIndependent K (fun i => (1-t) • v i + t • w i) := by
  classical
  let f := Fintype.linearCombination K v
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  have hgv (i : E) : g (v i) = Pi.single i 1 := by
    have h := LinearMap.congr_fun hg (Pi.single i 1)
    simpa [f, Fintype.linearCombination_apply] using h
  let M : Matrix E E (Polynomial K) := fun j i =>
    (1-Polynomial.X) * Polynomial.C (g (v i) j) + Polynomial.X * Polynomial.C (g (w i) j)
  have hM (t : K) : M.map (Polynomial.evalRingHom t) =
      (fun j i => g ((1-t) • v i + t • w i) j) := by
    ext j i
    change (Polynomial.evalRingHom t) (M j i) = _
    simp [M]
    ring
  have hzero : M.map (Polynomial.evalRingHom 0) = 1 := by
    rw [hM]
    ext j i
    by_cases h : j = i
    · subst j; simp [hgv]
    · simp [hgv, h]
  refine ⟨M.det, ?_, ?_⟩
  · change Polynomial.evalRingHom 0 M.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hzero, Matrix.det_one]
  · intro t ht
    have hu : IsUnit ((M.map (Polynomial.evalRingHom t)).det) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact isUnit_iff_ne_zero.mpr ht
    have hi := (Matrix.linearIndependent_cols_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    apply LinearIndependent.of_comp g
    rw [hM] at hi
    exact hi

end AffineIndependent
end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PointBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Multigraded
section AffineCokernel
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K W]

theorem affine_cokernel_polynomial (f g : V →ₗ[K] W) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      Module.finrank K (W ⧸ LinearMap.range ((1-t) • f + t • g)) ≤
        Module.finrank K (W ⧸ LinearMap.range f) := by
  classical
  let b := Module.finBasis K (LinearMap.range f)
  choose z hz using fun i => (b i).property
  have hli : LinearIndependent K (fun i => f (z i)) := by
    have h := b.linearIndependent.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
    simpa only [hz, Function.comp_def, Submodule.subtype_apply] using h
  obtain ⟨p,hp,hi⟩ := affine_independent_polynomial (fun i => f (z i))
    (fun i => g (z i)) hli
  refine ⟨p,hp,?_⟩
  intro t ht
  let ft : V →ₗ[K] W := (1-t) • f + t • g
  let bt : Fin (Module.finrank K (LinearMap.range f)) → LinearMap.range ft :=
    fun i => ⟨ft (z i), LinearMap.mem_range_self _ _⟩
  have htli : LinearIndependent K bt := by
    apply LinearIndependent.of_comp (LinearMap.range ft).subtype
    exact hi t ht
  have hb := htli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hb
  have hf := (LinearMap.range f).finrank_quotient_add_finrank
  have hg := (LinearMap.range ft).finrank_quotient_add_finrank
  dsimp only [ft] at hg hb
  omega

end AffineCokernel
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section GenericPieceBound
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]

theorem generic_homogeneous_quotient_bound (w : σ → G) (e : E → G)
    (F Q : E → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))
    (hQ : ∀ i, (Q i).IsWeightedHomogeneous w (e i))
    (d : G) [Module.Finite K (Piece (K := K) w d)] :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      Module.finrank K (componentQuotient w
        (Ideal.span (Set.range (fun i => (1-t) • Q i + t • F i))) d) ≤
      Module.finrank K (componentQuotient w (Ideal.span (Set.range Q)) d) := by
  obtain ⟨p,hp,h⟩ := affine_cokernel_polynomial
    (homogeneousIdealMap w e Q hQ d) (homogeneousIdealMap w e F hF d)
  refine ⟨p,hp,?_⟩
  intro t ht
  have h' := h t ht
  rw [← homogeneousIdealMap_affine w e F hF Q hQ d t] at h'
  rw [homogeneousIdealMap_range w e Q hQ d] at h'
  rw [homogeneousIdealMap_range] at h'
  exact h'

end GenericPieceBound

section ProductComparison
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem generic_product_piece_bound (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := K) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → K)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j)
    (F : Fin qs.length → MvPolynomial (BlockVariables a) K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      ((qs.get i).leftDegree + (qs.get i).rightDegree))
    (d : ι → ℤ) (hd : ∀ j, (qs.length : ℤ) < d j) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ c : K, p.eval c ≠ 0 →
      pieceDim (blockWeight (fun v : BlockVariables a => v.1))
        (Ideal.span (Set.range (fun i =>
          (1-c) • ((qs.get i).left * (qs.get i).right) + c • F i))) d ≤
      (mixedPolynomial u v).coeff a := by
  let w := blockWeight (fun v : BlockVariables a => v.1)
  obtain ⟨p,hp,h⟩ := generic_homogeneous_quotient_bound w
    (fun i => (qs.get i).leftDegree + (qs.get i).rightDegree) F
    (fun i => (qs.get i).left * (qs.get i).right) hF
    (fun i => (qs.get i).left_homogeneous.mul (qs.get i).right_homogeneous) d
  refine ⟨p,hp,?_⟩
  intro c hc
  apply (h c hc).trans
  rw [← productIdeal_eq_span]
  exact comparison_piece_bound a qs u v t ht hleft hright hdeg hlen d hd

end ProductComparison
end PermanentBorder.Multigraded

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Persistence
variable {C V : Type*}
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem isInvertible_iff_isUnit (T : V →L[ℂ] V) : T.IsInvertible ↔ IsUnit T := by
  constructor
  · intro h
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr h.bijective
  · intro h
    obtain ⟨U,hU⟩ := h
    exact ⟨ContinuousLinearEquiv.ofUnit U, hU⟩

omit [CompleteSpace C] in

theorem isOpen_simple {F : C × V → V} (hF : ContDiff ℂ 1 F) :
    IsOpen {u : C × V | SimpleAt F u.1 u.2} := by
  have hc : Continuous (fun u : C × V =>
      fderiv ℂ F u ∘L ContinuousLinearMap.inr ℂ C V) := by
    exact (hF.continuous_fderiv (by decide)).clm_comp continuous_const
  simpa only [SimpleAt, Prod.mk.eta, isInvertible_iff_isUnit, Set.preimage_ofPred_eq] using
    Units.isOpen.preimage hc

theorem simple_branch {F : C × V → V} (hF : ContDiff ℂ 1 F)
    {c : C} {x : V} (hz : F (c,x) = 0) (hs : SimpleAt F c x) :
    ∃ ψ : C → V, Tendsto ψ (𝓝 c) (𝓝 x) ∧
      ∀ᶠ c' in 𝓝 c, F (c', ψ c') = 0 ∧ SimpleAt F c' (ψ c') := by
  let hf := hF.contDiffAt (x := (c,x))
  let ψ := hf.implicitFunction (by decide) hs
  have ht : Tendsto ψ (𝓝 c) (𝓝 x) :=
    hf.hasStrictFDerivAt (by decide) |>.tendsto_implicitFunctionOfProdDomain hs
  refine ⟨ψ,ht,?_⟩
  have hz' := hf.eventually_apply_implicitFunction (by decide) hs
  have hne := (tendsto_id.prodMk_nhds ht).eventually ((isOpen_simple hF).mem_nhds hs)
  filter_upwards [hz', hne] with c' hc' hs'
  exact ⟨hc'.trans hz, hs'⟩

theorem finite_simple_zeros_persist {ι : Type*} [Fintype ι]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) {c : C}
    (x : ι → V) (hx : Function.Injective x)
    (hz : ∀ i, F (c,x i) = 0) (hs : ∀ i, SimpleAt F c (x i)) :
    ∀ᶠ c' in 𝓝 c, ∃ y : ι → V, Function.Injective y ∧
      ∀ i, F (c',y i) = 0 ∧ SimpleAt F c' (y i) := by
  classical
  choose ψ ht hψ using fun i => simple_branch hF (hz i) (hs i)
  have hall : ∀ᶠ c' in 𝓝 c, ∀ i, F (c',ψ i c') = 0 ∧ SimpleAt F c' (ψ i c') :=
    Filter.eventually_all.mpr hψ
  have hsep : ∀ᶠ c' in 𝓝 c, Function.Injective (fun i => ψ i c') := by
    have hp : ∀ i j : ι, ∀ᶠ c' in 𝓝 c, i ≠ j → ψ i c' ≠ ψ j c' := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall (by simp [hij])
      · have hh : (x i, x j) ∈ {p : V × V | p.1 ≠ p.2} := by
          exact fun h => hij (hx h)
        have ho : IsOpen {p : V × V | p.1 ≠ p.2} := isOpen_compl_iff.mpr (isClosed_eq continuous_fst continuous_snd)
        have he := ((ht i).prodMk_nhds (ht j)).eventually (ho.mem_nhds hh)
        exact he.mono fun _ h _ => h
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hp i))] with c' hc'
    intro i j he
    by_contra hij
    exact hc' i j hij he
  filter_upwards [hall,hsep] with c' hc' hi
  exact ⟨fun i => ψ i c',hi,hc'⟩
end Persistence
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
theorem fderiv_slice {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) (c : C) (x : V) :
    fderiv ℂ (fun x => F (c,x)) x =
      fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V := by
  have hi : HasFDerivAt (fun x : V => (c,x)) (ContinuousLinearMap.inr ℂ C V) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (𝕜 := ℂ) c x).prodMk (hasFDerivAt_id (𝕜 := ℂ) x)
  exact ((hF.differentiable (by decide) (c,x)).hasFDerivAt.comp x hi).fderiv

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open MvPolynomial
variable {τ : Type*} [Fintype τ]
theorem contDiff_mvPolynomial_eval (p : MvPolynomial τ ℂ) :
    ContDiff ℂ 1 (fun x : τ → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ 1 (fun _ : τ → ℂ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℂ ℂ i)

end PermanentBorder.PolarAnalysis

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ProjectiveCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectiveInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma projective_pair_separator (group : σ → ι) (x y : σ → K)
    (hxy : BlockSeparated group x y) :
    ∃ (p : MvPolynomial σ K) (e : ι → ℤ),
      p.IsWeightedHomogeneous (blockWeight group) e ∧
      (∀ j, 0 ≤ e j ∧ e j ≤ 1) ∧ eval x p = 1 ∧ eval y p = 0 := by
  classical
  obtain ⟨v,w,hvw,hxy⟩ := hxy
  let p : MvPolynomial σ K := C ((x v * y w - x w * y v)⁻¹) *
    (C (y w) * X v - C (y v) * X w)
  refine ⟨p, Pi.single (group v) 1, ?_, ?_, ?_, ?_⟩
  · apply IsWeightedHomogeneous.C_mul
    apply IsWeightedHomogeneous.sub
    · exact (isWeightedHomogeneous_X K (blockWeight group) v).C_mul _
    · simpa only [blockWeight, hvw] using
        (isWeightedHomogeneous_X K (blockWeight group) w).C_mul (y v)
  · intro j; by_cases h : j = group v <;> simp [h]
  · simp only [p, map_mul, eval_C, map_sub, eval_X]
    rw [mul_comm (y w), mul_comm (y v), inv_mul_cancel₀ (sub_ne_zero.mpr hxy)]
  · simp [p, mul_comm]

variable [Fintype L] [DecidableEq L]

theorem projective_interpolation (group : σ → ι) (d : ι → ℤ)
    (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (hb : ∀ i j, x i (base i j) ≠ 0) :
    ∃ p : L → Piece (K := K) (blockWeight group) d,
      ∀ i j, eval (x j) (p i).val = if j = i then 1 else 0 := by
  classical
  have hs (i j : L) : ∃ (p : MvPolynomial σ K) (e : ι → ℤ),
      p.IsWeightedHomogeneous (blockWeight group) e ∧
      (∀ l, 0 ≤ e l ∧ e l ≤ 1) ∧ eval (x i) p = 1 ∧ (i ≠ j → eval (x j) p = 0) := by
    by_cases hij : i = j
    · refine ⟨1,0,isWeightedHomogeneous_one _ _,?_,by simp,?_⟩
      · intro l; simp
      · exact fun h => (h hij).elim
    · obtain ⟨p,e,hp,he,hi,hj⟩ := projective_pair_separator group (x i) (x j) (hx i j hij)
      exact ⟨p,e,hp,he,hi,fun _ => hj⟩
  choose p e hp he hi hj using hs
  let E : L → ι → ℤ := fun i => ∑ j, e i j
  have hE (i : L) (l : ι) : E i l ≤ Fintype.card L := by
    dsimp [E]
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (he i j l).2)
  let b : L → ι → ℕ := fun i l => (d l - E i l).toNat
  have hbdeg (i : L) : (fun l => (b i l : ℤ)) = d-E i := by
    funext l
    exact Int.toNat_of_nonneg (sub_nonneg.mpr ((hE i l).trans (hd l)))
  let pad : L → MvPolynomial σ K := fun i =>
    ∏ l, (C ((x i (base i l))⁻¹) * X (base i l)) ^ b i l
  have hpadhom (i : L) : (pad i).IsWeightedHomogeneous (blockWeight group) (d - E i) := by
    rw [← hbdeg]
    have h := IsWeightedHomogeneous.prod Finset.univ
      (fun l => (C ((x i (base i l))⁻¹) * X (base i l) : MvPolynomial σ K)^b i l)
      (fun l => b i l • Pi.single l (1 : ℤ)) (fun l _ => by
        convert ((isWeightedHomogeneous_X K (blockWeight group) (base i l)).C_mul
          ((x i (base i l))⁻¹)).pow (b i l) using 1
        simp only [blockWeight, hbase])
    convert h using 1
    ext l
    simp [Pi.single_apply]
  have hpadeval (i : L) : eval (x i) (pad i) = 1 := by
    simp [pad, inv_mul_cancel₀ (hb i _)]
  let P : L → MvPolynomial σ K := fun i => (∏ j, p i j) * pad i
  have hPhom (i : L) : (P i).IsWeightedHomogeneous (blockWeight group) d := by
    have hp' := IsWeightedHomogeneous.prod Finset.univ (p i) (e i) (fun j _ => hp i j)
    have h := hp'.mul (hpadhom i)
    have hdeg : (∑ j, e i j) + (d - E i) = d := by dsimp [E]; abel
    rw [hdeg] at h
    exact h
  refine ⟨fun i => ⟨P i,hPhom i⟩,?_⟩
  intro i j
  change eval (x j) (P i) = _
  simp only [P, map_mul, map_prod]
  by_cases hij : j = i
  · subst j
    simp [hi, hpadeval]
  · rw [ite_eq_right hij, Finset.prod_eq_zero (Finset.mem_univ j) (hj i j (Ne.symm hij)), zero_mul]

end ProjectiveInterpolation
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectivePointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

theorem projective_points_le_pieceDim (group : σ → ι) (base : L → ι → σ)
    (hbase : ∀ i j, group (base i j) = j) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    (hb : ∀ i j, x i (base i j) ≠ 0)
    (hz : ∀ i, ∀ p ∈ I, eval (x i) p = 0) :
    Fintype.card L ≤ Module.finrank K (componentQuotient (blockWeight group) I d) := by
  classical
  let P := Piece (K := K) (blockWeight group) d
  let S : Submodule K P := (I.restrictScalars K).comap P.subtype
  let ev : P →ₗ[K] (L → K) := LinearMap.pi fun i =>
    (aeval (x i)).toLinearMap.comp P.subtype
  have heval (p : P) (i : L) : ev p i = eval (x i) p.val := by
    simp [ev]
  have hker : S ≤ LinearMap.ker ev := by
    intro p hp
    apply LinearMap.mem_ker.mpr
    funext i
    rw [heval]
    exact hz i p.val hp
  let qev := S.liftQ ev hker
  obtain ⟨p,hp⟩ := projective_interpolation group d hd x hx base hbase hb
  have hs : Function.Surjective qev := by
    intro y
    refine ⟨S.mkQ (∑ i, y i • p i), ?_⟩
    change ev (∑ i, y i • p i) = y
    apply _root_.funext
    intro j
    have hei (i : L) : ev (p i) j = if j = i then 1 else 0 :=
      (heval (p i) j).trans (hp i j)
    calc
      ev (∑ i, y i • p i) j = ∑ i, y i * ev (p i) j := by simp
      _ = y j := by simp [hei]
  have h := LinearMap.finrank_le_finrank_of_surjective hs
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using h

end ProjectivePointBound
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section MultiChartProductCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

omit [Fintype ι] [DecidableEq ι] in

lemma eventually_blockSeparated {σ : Type*} (group : σ → ι)
    (x : L → σ → ℂ) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    {y : L → ℂ → σ → ℂ} {c : ℂ}
    (hy : ∀ i, Tendsto (y i) (𝓝 c) (𝓝 (x i))) :
    ∀ᶠ c' in 𝓝 c, ∀ i j, i ≠ j → BlockSeparated group (y i c') (y j c') := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
  obtain ⟨v,w,hvw,hn⟩ := hx i j hij
  have hv₁ := (continuous_apply v).tendsto (x i) |>.comp (hy i)
  have hw₁ := (continuous_apply w).tendsto (x i) |>.comp (hy i)
  have hv₂ := (continuous_apply v).tendsto (x j) |>.comp (hy j)
  have hw₂ := (continuous_apply w).tendsto (x j) |>.comp (hy j)
  have he := ((hv₁.mul hw₂).sub (hw₁.mul hv₂)).eventually_ne (sub_ne_zero.mpr hn)
  exact he.mono (fun c' hc' _ => ⟨v,w,hvw,sub_ne_zero.mp hc'⟩)

theorem product_simple_point_bound_multichart (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := ℂ) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → ℂ)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j)
    (F : Fin qs.length → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      ((qs.get i).leftDegree + (qs.get i).rightDegree))
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin qs.length → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let Q : Fin qs.length → MvPolynomial (BlockVariables a) ℂ :=
    fun j => (qs.get j).left * (qs.get j).right
  let family : L → ℂ × V → V := fun i z => e i
    (fun j => (1-z.1) * eval (chart i z.2) (Q j) + z.1 * eval (chart i z.2) (F j))
  have hcont (i : L) : ContDiff ℂ 1 (family i) := by
    apply (e i).contDiff.comp
    apply contDiff_pi.mpr
    intro j
    exact ((contDiff_const.sub contDiff_fst).mul
      ((PolarAnalysis.contDiff_mvPolynomial_eval (Q j)).comp ((hc i).comp contDiff_snd))).add
      (contDiff_fst.mul
        ((PolarAnalysis.contDiff_mvPolynomial_eval (F j)).comp ((hc i).comp contDiff_snd)))
  have hone (i : L) : (fun z => family i (1,z)) =
      (fun z => e i (fun j => eval (chart i z) (F j))) := by
    funext z
    simp [family]
  have hzero (i : L) : family i (1,x i) = 0 := by
    rw [congrFun (hone i)]
    rw [show (fun j => eval (chart i (x i)) (F j)) = 0 from funext (hz i), map_zero]
  have hsimple (i : L) : PolarAnalysis.SimpleAt (family i) 1 (x i) := by
    unfold PolarAnalysis.SimpleAt
    rw [← PolarAnalysis.fderiv_slice (hcont i), hone]
    exact hs i
  choose ψ hψ hzψ using fun i => PolarAnalysis.simple_branch (hcont i) (hzero i) (hsimple i)
  have hsep := eventually_blockSeparated (fun v : BlockVariables a => v.1)
    (fun i => chart i (x i)) hx (fun i => (hc i).continuous.continuousAt.tendsto.comp (hψ i))
  have hpersist : ∀ᶠ c in 𝓝 (1 : ℂ),
      (∀ i, family i (c,ψ i c) = 0) ∧
      ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
        (chart i (ψ i c)) (chart j (ψ j c)) := by
    filter_upwards [Filter.eventually_all.mpr hzψ, hsep] with c hz hc
    exact ⟨fun i => (hz i).1,hc⟩
  let d : ι → ℤ := fun _ => qs.length + Fintype.card L + 1
  obtain ⟨p,hp,hbound⟩ := generic_product_piece_bound a qs u v t ht hleft hright hdeg
    hlen F hF d (by intro j; dsimp [d]; omega)
  have hpne : p ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at hp
    exact zero_ne_one hp
  have hdense : Dense {c : ℂ | p.eval c ≠ 0} :=
    (Polynomial.finite_setOfPred_isRoot hpne).countable.dense_compl ℂ
  obtain ⟨c,hpc,hyz,hy⟩ := hdense.inter_nhds_nonempty hpersist
  let I := Ideal.span (Set.range (fun j => (1-c) • Q j + c • F j))
  have hyideal (i : L) : ∀ p ∈ I, eval (chart i (ψ i c)) p = 0 := by
    have hI : I ≤ RingHom.ker (eval (chart i (ψ i c))) := by
      apply Ideal.span_le.mpr
      rintro p ⟨j,rfl⟩
      change eval (chart i (ψ i c)) ((1-c) • Q j + c • F j) = 0
      have h := (e i).injective ((hyz i).trans (map_zero (e i)).symm)
      have h := congrFun h j
      simpa only [map_add, smul_eval, Pi.zero_apply] using h
    exact fun p hp => hI hp
  have hpoints := projective_points_le_pieceDim (fun v : BlockVariables a => v.1)
    base hbase I d (by intro j; dsimp [d]; omega) (fun i => chart i (ψ i c)) hy
    (fun i j => by rw [hcn]; exact one_ne_zero) hyideal
  exact hpoints.trans (hbound c hpc)

end MultiChartProductCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearMultiChartCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem bilinear_simple_point_count_multichart (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (hM : M = ∑ j, a j)
    (F : Fin M → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin M → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let t : (Fin M × Bool) → ℂ := fun i =>
    Infinite.natEmbedding ℂ ((Fintype.equivFin (Fin M × Bool) i).val)
  have ht : Function.Injective t :=
    (Infinite.natEmbedding ℂ).injective.comp
      (Fin.val_injective.comp (Fintype.equivFin (Fin M × Bool)).injective)
  generalize hqs : List.ofFn (vandermondePairs a u v t) = qs
  have hlen : qs.length = M := by rw [← hqs, List.length_ofFn]
  cases hlen
  have hget (i : Fin qs.length) : qs.get i = vandermondePairs a u v t i := by
    have h := congrArg (fun l => l[i.val]?) hqs
    simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, List.getElem?_eq_getElem i.isLt,
      Option.some.injEq, List.get_eq_getElem] using h.symm
  apply product_simple_point_bound_multichart a qs u v t ht
    (fun i => by rw [hget]; rfl) (fun i => by rw [hget]; rfl) ?_ hM F
    (by intro i; simpa only [hget, vandermondePairs] using hF i)
    base hbase e chart hc hcn x hx hz hs
  intro q hq j
  rw [← hqs] at hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  by_cases hj : j = u i <;> simp [vandermondePairs, hj]

end BilinearMultiChartCount
end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.KernelCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

lemma weight_mapDomain_eq {σ τ G : Type*} [AddCommMonoid G]
    (w : σ → G) (w' : τ → G) (f : σ → τ) (hf : ∀ x, w' (f x) = w x)
    (d : σ →₀ ℕ) : Finsupp.weight w' (d.mapDomain f) = Finsupp.weight w d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp [Finsupp.mapDomain_add, hd, he]
  | single x n => simp [Finsupp.weight_single, hf]

lemma homogeneous_rename {σ τ G R : Type*} [AddCommMonoid G] [CommSemiring R]
    (w : σ → G) (w' : τ → G) (f : σ → τ) (hf : ∀ x, w' (f x) = w x)
    {p : MvPolynomial σ R} {d : G} (hp : p.IsWeightedHomogeneous w d) :
    (rename f p).IsWeightedHomogeneous w' d := by
  conv_lhs => rw [as_sum p]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ ((weight_mapDomain_eq w w' f hf m).trans
    (hp (mem_support_iff.mp hm)))

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem bilinear_simple_point_count_reindex (a : ι →₀ ℕ)
    (group : σ → ι) (ve : σ ≃ BlockVariables a)
    (hv : ∀ s, (ve s).1 = group s)
    (u v : E → ι) (hM : Fintype.card E = ∑ j, a j)
    (F : E → MvPolynomial σ ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (blockWeight group)
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (e : L → (E → ℂ) ≃L[ℂ] V)
    (chart : L → V → σ → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated group (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let ee := (Fintype.equivFin E).symm
  let ec : (Fin (Fintype.card E) → ℂ) ≃L[ℂ] (E → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : E => ℂ) ee
  let F' (i : Fin (Fintype.card E)) := rename ve (F (ee i))
  let chart' (i : L) (z : V) : BlockVariables a → ℂ := chart i z ∘ ve.symm
  have hc' (i : L) : ContDiff ℂ 1 (chart' i) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_apply ℂ ℂ (ve.symm j)).comp (hc i)
  have heval (i : L) (z : V) (j : Fin (Fintype.card E)) :
      eval (chart' i z) (F' j) = eval (chart i z) (F (ee j)) := by
    dsimp only [F']
    rw [eval_rename]
    apply congrArg (fun v : σ → ℂ => eval v (F (ee j)))
    funext s
    simp [chart']
  have hs' (i : L) : (fun z => (ec.trans (e i)) (fun j => eval (chart' i z) (F' j))) =
      fun z => e i (fun j => eval (chart i z) (F j)) := by
    funext z
    simp only [ContinuousLinearEquiv.trans_apply]
    apply congrArg (e i)
    funext j
    change (Homeomorph.piCongrLeft (Y := fun _ : E => ℂ) ee)
      (fun j => eval (chart' i z) (F' j)) j = _
    conv_lhs => rw [← ee.apply_symm_apply j]
    rw [Homeomorph.piCongrLeft_apply_apply, heval, ee.apply_symm_apply]
  have hh := bilinear_simple_point_count_multichart a (u ∘ ee) (v ∘ ee) hM F'
    (fun i => homogeneous_rename _ _ ve (fun s => by simp [blockWeight, hv]) (hF (ee i)))
    (fun i j => ve (base i j)) (fun i j => (hv _).trans (hbase i j))
    (fun i => ec.trans (e i)) chart' hc'
    (fun i z j => by simpa [chart'] using hcn i z j) x
    (fun i j hij => by
      obtain ⟨s,t,hst,hne⟩ := hx i j hij
      refine ⟨ve s,ve t,?_,?_⟩
      · simpa [hv] using hst
      · simpa [chart'] using hne)
    (fun i j => (heval i (x i) j).trans (hz i (ee j)))
    (fun i => by rw [hs']; exact hs i)
  have hm : mixedPolynomial (u ∘ ee) (v ∘ ee) = mixedPolynomial u v := by
    exact Fintype.prod_equiv ee _ _ (fun _ => rfl)
  rwa [hm] at hh
end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

variable {κ : Type} [Fintype κ] {n : ℕ}

lemma linearMatrix_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin (n+1)) :
    (linearMatrix A₀ A i j).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single none 1) := by
  apply IsWeightedHomogeneous.add
  · exact (isWeightedHomogeneous_X ℂ _ _).C_mul _
  · exact IsWeightedHomogeneous.sum _ _ _ (fun k _ => (isWeightedHomogeneous_X ℂ _ _).C_mul _)

lemma right_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i : Fin (n+1)) :
    (rightEquation A₀ A i).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (none : Groups) 1 + Pi.single (some false) 1) := by
  unfold rightEquation
  apply IsWeightedHomogeneous.sum
  intro j _
  exact (linearMatrix_homogeneous A₀ A i j).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some false,j⟩ : Variables κ n))

lemma left_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (j : Fin (n+1)) :
    (leftEquation A₀ A j).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (none : Groups) 1 + Pi.single (some true) 1) := by
  unfold leftEquation
  apply IsWeightedHomogeneous.sum
  intro i _
  exact (linearMatrix_homogeneous A₀ A i j).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some true,i⟩ : Variables κ n))

omit [Fintype κ] in
lemma polar_homogeneous (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (polarEquation (κ := κ) B).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (some false : Groups) 1 + Pi.single (some true) 1) := by
  unfold polarEquation
  apply IsWeightedHomogeneous.sum
  intro i _
  apply IsWeightedHomogeneous.sum
  intro j _
  exact ((isWeightedHomogeneous_X ℂ _ (⟨some false,j⟩ : Variables κ n)).C_mul (B i j)).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some true,i⟩ : Variables κ n))

lemma system_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (pivot : Fin (n+1))
    (i : Equations κ n) :
    (system A₀ A B pivot i).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (firstGroup i) 1 + Pi.single (secondGroup i) 1) := by
  rcases i with i | j | k
  · exact right_homogeneous A₀ A i
  · exact left_homogeneous A₀ A (pivot.succAbove j)
  · exact polar_homogeneous (B k)

lemma card_equations : Fintype.card (Equations κ n) = ∑ j, dimensions κ n j := by
  simp [Equations, Fintype.sum_option]
  omega

lemma mixedPolynomial_eq :
    Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup =
      (X none + X (some false))^(n+1) * (X none + X (some true))^n *
        (X (some false) + X (some true))^Fintype.card κ := by
  simp [Multigraded.mixedPolynomial, firstGroup, secondGroup, Fintype.prod_sum_type,
    mul_assoc]

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]

lemma collapse_monomial (i : σ) (d : σ →₀ ℕ) (a : ℕ) :
    collapse i (monomial d a) = Polynomial.C a * Polynomial.X^(d i) := by
  rw [collapse, eval₂Hom_monomial]
  congr 1
  have h := Finsupp.prod_ite_eq d i (fun _ n => (Polynomial.X : Polynomial ℕ)^n)
  by_cases hi : i ∈ d.support
  · simpa only [ite_eq_left hi, eq_comm, ite_pow, one_pow] using h
  · simpa only [ite_eq_right hi, Finsupp.notMem_support_iff.mp hi, pow_zero,
      eq_comm, ite_pow, one_pow] using h

lemma coeff_le_collapse (i : σ) (p : MvPolynomial σ ℕ) (d : σ →₀ ℕ) :
    p.coeff d ≤ (collapse i p).coeff (d i) := by
  by_cases hd : d ∈ p.support
  · have he : (collapse i p).coeff (d i) =
        ∑ k ∈ p.support, (collapse i (monomial k (p.coeff k))).coeff (d i) := by
      conv_lhs => rw [as_sum p]
      simp only [map_sum, Polynomial.finsetSum_coeff]
    rw [he]
    have h := Finset.single_le_sum (fun k (_ : k ∈ p.support) =>
      Nat.zero_le ((collapse i (monomial k (p.coeff k))).coeff (d i))) hd
    simpa [collapse_monomial, Polynomial.coeff_C_mul] using h
  · rw [notMem_support_iff.mp hd]
    exact Nat.zero_le _
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
lemma mixed_coefficient_bound :
    (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup).coeff
      (dimensions κ n) ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  have h := Multigraded.coeff_le_collapse none
    (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup)
    (dimensions κ n)
  have hp : Multigraded.collapse none
      (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup) =
      (Polynomial.X + 1)^(2*n+1) * Polynomial.C (2^Fintype.card κ) := by
    rw [mixedPolynomial_eq]
    simp only [map_mul, map_pow, map_add, Multigraded.collapse, eval₂Hom_X']
    simp only [↓reduceIte, Option.some_ne_none, one_add_one_eq_two]
    rw [← pow_add, show n+1+n = 2*n+1 by omega]
    simp
  rw [hp, dimensions_none, Polynomial.coeff_mul_C, Polynomial.coeff_X_add_one_pow,
    mul_comm] at h
  exact h
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

 theorem isInvertible_of_injective (T : V →L[ℂ] V) (hT : Function.Injective T) :
    T.IsInvertible := by
  have hs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hT,hs⟩
  exact ⟨ContinuousLinearEquiv.ofUnit u,hu⟩

theorem invertible_elimination (R : (V × W) →L[ℂ] V) (E : (V × W) →L[ℂ] W)
    (g : V →L[ℂ] W)
    (hE : (E ∘L ContinuousLinearMap.inr ℂ V W).IsInvertible)
    (he : E ∘L ((ContinuousLinearMap.id ℂ V).prod g) = 0)
    (hR : (R ∘L ((ContinuousLinearMap.id ℂ V).prod g)).IsInvertible) :
    (R.prod E).IsInvertible := by
  apply isInvertible_of_injective
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  have hrz : R z = 0 := congrArg Prod.fst hz
  have hez : E z = 0 := congrArg Prod.snd hz
  have heg : E (z.1,g z.1) = 0 := by
    have h := congrArg (fun T : (V →L[ℂ] W) => T z.1) he
    simpa using h
  have hsub : E (0,z.2-g z.1) = 0 := by
    have hh : (0,z.2-g z.1) = z - (z.1,g z.1) := by ext <;> simp
    rw [hh, map_sub,hez,heg,sub_self]
  have hdw : z.2 = g z.1 := by
    have hm : (E ∘L ContinuousLinearMap.inr ℂ V W) (z.2-g z.1) =
        (E ∘L ContinuousLinearMap.inr ℂ V W) 0 := by
      rw [map_zero]
      exact hsub
    exact sub_eq_zero.mp (hE.bijective.injective hm)
  have hdx : z.1 = 0 := by
    apply hR.bijective.injective
    rw [map_zero]
    change R (z.1,g z.1) = 0
    simpa only [← hdw,Prod.eta] using hrz
  exact Prod.ext hdx (by simpa [hdx] using hdw)

theorem simple_after_elimination {R : V × W → V} {E : V × W → W}
    {g : V → W} {x : V}
    (hR : DifferentiableAt ℂ R (x,g x)) (hE : DifferentiableAt ℂ E (x,g x))
    (hg : DifferentiableAt ℂ g x)
    (he : (fun y => E (y,g y)) =ᶠ[𝓝 x] 0)
    (haux : (fderiv ℂ E (x,g x) ∘L ContinuousLinearMap.inr ℂ V W).IsInvertible)
    (hs : (fderiv ℂ (fun y => R (y,g y)) x).IsInvertible) :
    (fderiv ℂ (fun z => (R z,E z)) (x,g x)).IsInvertible := by
  let graph := (ContinuousLinearMap.id ℂ V).prod (fderiv ℂ g x)
  have hgraph : HasFDerivAt (fun y => (y,g y)) graph x :=
    (hasFDerivAt_id x).prodMk hg.hasFDerivAt
  have he' : fderiv ℂ E (x,g x) ∘L graph = 0 := by
    have hd := hE.hasFDerivAt.comp x hgraph
    have hz := (hasFDerivAt_const (𝕜 := ℂ) (0 : W) x).congr_of_eventuallyEq he
    exact hd.unique hz
  have hr' : (fderiv ℂ R (x,g x) ∘L graph).IsInvertible := by
    have hd := hR.hasFDerivAt.comp x hgraph
    rwa [← hd.fderiv]
  rw [(hR.hasFDerivAt.prodMk hE.hasFDerivAt).fderiv]
  exact invertible_elimination _ _ _ haux he' hr'
end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem solved_right (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    block a β γ E *ᵥ normalized (right γ E) =
      Sum.elim (fun _ => scalar a β γ E) (fun _ => 0) := by
  have hu : IsUnit E.det := isUnit_iff_ne_zero.mpr hE
  simp only [block, normalized, fromBlocks_mulVec, right, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hh : E *ᵥ -(E⁻¹ *ᵥ γ) = -γ := by
    rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv E hu, one_mulVec]
  rw [hh]
  ext j
  cases j <;> simp [scalar, mulVec, dotProduct, Finset.mul_sum, sub_eq_add_neg]

 theorem solved_left (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    normalized (left β E) ᵥ* block a β γ E =
      Sum.elim (fun _ => scalar a β γ E) (fun _ => 0) := by
  have hu : IsUnit E.det := isUnit_iff_ne_zero.mpr hE
  simp only [block, normalized, vecMul_fromBlocks, left, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hh : -(β ᵥ* E⁻¹) ᵥ* E = -β := by
    rw [neg_vecMul, vecMul_vecMul, nonsing_inv_mul E hu, vecMul_one]
  rw [hh]
  ext j
  cases j with
  | inl u =>
    simp only [Sum.elim_inl, Pi.add_apply, vecMul, dotProduct, Matrix.of_apply,
      Fintype.sum_unique, one_mul, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
      scalar, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc, sub_eq_add_neg]
    rw [Finset.sum_comm]
  | inr j => simp [vecMul, dotProduct]

 theorem det_block (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    (block a β γ E).det = E.det * scalar a β γ E := by
  let := E.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hE)
  rw [block, det_fromBlocks₂₂]
  congr 1
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  simp only [Matrix.sub_apply, Matrix.mul_apply, scalar]
  simp only [invOf_eq_nonsing_inv, Matrix.of_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_det {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (fun y => (E y).det) x := by
  classical
  simp only [Matrix.det_apply]
  fun_prop

 theorem differentiableAt_adjugate {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply differentiableAt_det
  intro u v
  by_cases hu : u = j
  · subst u
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simpa only [Matrix.updateRow_ne hu] using hE u v

 theorem differentiableAt_inverse {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((differentiableAt_det hE).inv hx).mul (differentiableAt_adjugate hE i j)
end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SchurDifferentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_right {γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i : ι) :
    DifferentiableAt ℂ (fun y => right (γ y) (E y) i) x := by
  simp only [right, Pi.neg_apply, mulVec, dotProduct]
  exact (DifferentiableAt.fun_sum (fun j _ =>
    (differentiableAt_inverse hE hx i j).mul (hγ j))).neg

 theorem differentiableAt_left {β : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i : ι) :
    DifferentiableAt ℂ (fun y => left (β y) (E y) i) x := by
  simp only [left, Pi.neg_apply, vecMul, dotProduct]
  exact (DifferentiableAt.fun_sum (fun j _ =>
    (hβ j).mul (differentiableAt_inverse hE hx j i))).neg

omit [Fintype ι] [DecidableEq ι] in
 theorem differential_mulVec {κ : Type*} [Fintype κ]
    {A : V → Matrix ι κ ℂ} {p : V → κ → ℂ} {x : V}
    (hA : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x)
    (hp : ∀ i, DifferentiableAt ℂ (fun y => p y i) x) (h : V) (i : ι) :
    fderiv ℂ (fun y => (A y *ᵥ p y) i) x h =
      ((Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h) *ᵥ p x) i +
      (A x *ᵥ (fun j => fderiv ℂ (fun y => p y j) x h)) i := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hA i j).hasFDerivAt.mul (hp j).hasFDerivAt)
  have heq : fderiv ℂ (fun y => (A y *ᵥ p y) i) x =
      ∑ j, ((A x i j) • fderiv ℂ (fun y => p y j) x +
        (p x j) • fderiv ℂ (fun y => A y i j) x) := by
    convert! hd.fderiv using 1
  rw [heq]
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Finset.sum_add_distrib, Matrix.of_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

 theorem differential_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {x : V}
    (ha : DifferentiableAt ℂ a x)
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (h : V) :
    fderiv ℂ (fun y => scalar (a y) (β y) (γ y) (E y)) x h =
      normalized (left (β x) (E x)) ⬝ᵥ
        ((Matrix.of fun i j => fderiv ℂ (fun y => block (a y) (β y) (γ y) (E y) i j) x h)
          *ᵥ normalized (right (γ x) (E x))) := by
  let A := fun y => block (a y) (β y) (γ y) (E y)
  let p := fun y => normalized (right (γ y) (E y))
  let b := normalized (left (β x) (E x))
  let S := fun y => scalar (a y) (β y) (γ y) (E y)
  have hA : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x := by
    intro i j
    cases i <;> cases j <;> simp only [A, block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply]
    · exact ha
    · exact hβ _
    · exact hγ _
    · exact hE _ _
  have hp : ∀ i, DifferentiableAt ℂ (fun y => p y i) x := by
    intro i
    cases i with
    | inl u => exact differentiableAt_const _
    | inr i => exact differentiableAt_right hγ hE hx i
  have hevent : ∀ᶠ y in 𝓝 x, (E y).det ≠ 0 :=
    (differentiableAt_det hE).continuousAt.eventually_ne hx
  have heq (i : Unit ⊕ ι) :
      (fun y => (A y *ᵥ p y) i) =ᶠ[𝓝 x] (fun y => Sum.elim (fun _ => S y) (fun _ => 0) i) := by
    filter_upwards [hevent] with y hy
    exact congr_fun (solved_right (a y) (β y) (γ y) (E y) hy) i
  let dA : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
    Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h
  let dp : Unit ⊕ ι → ℂ := fun j => fderiv ℂ (fun y => p y j) x h
  have hd : dA *ᵥ p x + A x *ᵥ dp =
      Sum.elim (fun _ => fderiv ℂ S x h) (fun _ => 0) := by
    ext i
    change (dA *ᵥ p x) i + (A x *ᵥ dp) i = _
    rw [← differential_mulVec hA hp h i]
    rw [(heq i).fderiv_eq]
    cases i <;> simp
  have hb : b ᵥ* A x = Sum.elim (fun _ => S x) (fun _ => 0) :=
    solved_left (a x) (β x) (γ x) (E x) hx
  have hz : b ⬝ᵥ (A x *ᵥ dp) = 0 := by
    rw [dotProduct_mulVec, hb]
    simp [dotProduct, dp, p, normalized, Fintype.sum_sum_type]
  have hd' := congrArg (fun z => b ⬝ᵥ z) hd
  rw [dotProduct_add, hz, add_zero] at hd'
  change fderiv ℂ S x h = b ⬝ᵥ (dA *ᵥ p x)
  simpa [dotProduct, b, normalized, Fintype.sum_sum_type] using hd'.symm
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem auxiliaryLinear_invertible (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    (auxiliaryLinear E).IsInvertible := by
  have hu := isUnit_iff_ne_zero.mpr hE
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := auxiliaryLinear E⁻¹)
  · apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext <;> simp [mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv E hu,
      nonsing_inv_mul E hu]
  · apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext <;> simp [mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv E hu,
      nonsing_inv_mul E hu]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
 theorem auxiliary_solved (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (x : V) (hx : (E x).det ≠ 0) :
    auxiliary β γ E (x,graphKernels β γ E x) = 0 := by
  have hu := isUnit_iff_ne_zero.mpr hx
  apply Prod.ext <;> simp [auxiliary, graphKernels, right, left, mulVec_neg, neg_vecMul,
    mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv (E x) hu, nonsing_inv_mul (E x) hu]

 theorem differentiableAt_graphKernels {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) : DifferentiableAt ℂ (graphKernels β γ E) x := by
  apply DifferentiableAt.prodMk
  · exact differentiableAt_pi.mpr (differentiableAt_right hγ hE hx)
  · exact differentiableAt_pi.mpr (differentiableAt_left hβ hE hx)

omit [DecidableEq ι] in
 theorem differentiableAt_auxiliary {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ}
    {x : V} {w : (ι → ℂ) × (ι → ℂ)}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (auxiliary β γ E) (x,w) := by
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr
    intro i
    change DifferentiableAt ℂ (fun z => γ z.1 i + ∑ j, E z.1 i j * z.2.1 j) (x,w)
    apply DifferentiableAt.add ((hγ i).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    apply DifferentiableAt.fun_sum
    intro j _
    apply DifferentiableAt.mul ((hE i j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    fun_prop
  · apply differentiableAt_pi.mpr
    intro j
    change DifferentiableAt ℂ (fun z => β z.1 j + ∑ i, z.2.2 i * E z.1 i j) (x,w)
    apply DifferentiableAt.add ((hβ j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.mul _ ((hE i j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    fun_prop

omit [DecidableEq ι] in
 theorem fderiv_auxiliary_inr {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ}
    {x : V} {w : (ι → ℂ) × (ι → ℂ)}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    fderiv ℂ (auxiliary β γ E) (x,w) ∘L ContinuousLinearMap.inr ℂ V _ =
      auxiliaryLinear (E x) := by
  have hd := (differentiableAt_auxiliary (w := w) hβ hγ hE).hasFDerivAt.comp w
    ((hasFDerivAt_const x w).prodMk (hasFDerivAt_id w))
  have hf : HasFDerivAt (fun v => auxiliary β γ E (x,v)) (auxiliaryLinear (E x)) w := by
    convert! (auxiliaryLinear (E x)).hasFDerivAt.const_add (γ x,β x) using 1
  convert! hd.unique hf using 1

 theorem simple_kernel_elimination [FiniteDimensional ℂ V]
    {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    {R : V × ((ι → ℂ) × (ι → ℂ)) → V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0)
    (hR : DifferentiableAt ℂ R (x,graphKernels β γ E x))
    (hs : (fderiv ℂ (fun y => R (y,graphKernels β γ E y)) x).IsInvertible) :
    (fderiv ℂ (fun z => (R z,auxiliary β γ E z))
      (x,graphKernels β γ E x)).IsInvertible := by
  apply PermanentBorder.PolarAnalysis.simple_after_elimination hR
    (differentiableAt_auxiliary hβ hγ hE) (differentiableAt_graphKernels hβ hγ hE hx)
  · have he := (differentiableAt_det hE).continuousAt.eventually_ne hx
    filter_upwards [he] with y hy
    exact auxiliary_solved β γ E y hy
  · rw [fderiv_auxiliary_inr hβ hγ hE]
    exact auxiliaryLinear_invertible _ hx
  · exact hs
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem contDiff_det {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) :
    ContDiff ℂ n (fun y => (E y).det) := by
  classical
  simp only [Matrix.det_apply]
  fun_prop

 theorem contDiff_adjugate {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) (i j : ι) :
    ContDiff ℂ n (fun y => (E y).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det
  intro u v
  by_cases hu : u = j
  · subst u
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow_ne hu] using hE u v

 theorem contDiffAt_inverse {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞} {x : V}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j))
    (hx : (E x).det ≠ 0) (i j : ι) :
    ContDiffAt ℂ n (fun y => (E y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiff_det hE).contDiffAt.inv hx).mul (contDiff_adjugate hE i j).contDiffAt

 theorem contDiffAt_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞} {x : V}
    (ha : ContDiff ℂ n a)
    (hβ : ∀ i, ContDiff ℂ n (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ n (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j))
    (hx : (E x).det ≠ 0) :
    ContDiffAt ℂ n (fun y => scalar (a y) (β y) (γ y) (E y)) x := by
  simp only [scalar, mulVec, dotProduct]
  exact ha.contDiffAt.sub (ContDiffAt.sum (fun j _ => (hβ j).contDiffAt.mul
    (ContDiffAt.sum (fun l _ => (contDiffAt_inverse hE hx j l).mul (hγ l).contDiffAt))))
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem simple_unit_multiplier_iff {T : E → (F →L[ℂ] F)} {g : E → F} {x : E}
    (hT : DifferentiableAt ℂ T x) (hg : DifferentiableAt ℂ g x)
    (hz : g x = 0) (hu : (T x).IsInvertible) :
    (fderiv ℂ (fun y => T y (g y)) x).IsInvertible ↔ (fderiv ℂ g x).IsInvertible := by
  rw [fderiv_clm_apply hT hg, hz, map_zero, add_zero]
  obtain ⟨e,he⟩ := hu
  rw [← he]
  exact ContinuousLinearMap.isInvertible_equiv_comp

 theorem triangularMultiplier_invertible (c : ℂ) (d : F) (hc : c ≠ 0) :
    (triangularMultiplier c d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := triangularMultiplier c⁻¹ (-((c⁻¹*c⁻¹) • d)))
  · ext z <;> simp [smul_smul, hc]
  · ext z <;> simp [smul_smul, hc]

 theorem differentiableAt_triangularMultiplier {c : E → ℂ} {d : E → F} {x : E}
    (hc : DifferentiableAt ℂ c x) (hd : DifferentiableAt ℂ d x) :
    DifferentiableAt ℂ (fun y => triangularMultiplier (c y) (d y)) x := by
  apply DifferentiableAt.add (hc.smul_const _) ?_
  apply (differentiableAt_const (c := ContinuousLinearMap.inr ℂ ℂ F)).clm_comp
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × F) F
    (ContinuousLinearMap.fst ℂ ℂ F)).differentiableAt.comp x hd)

end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

 theorem differentiableAt_polarPair {F : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hF : ContDiffAt ℂ 2 F (ψ x)) (hψ : DifferentiableAt ℂ ψ x) :
    DifferentiableAt ℂ (polarPair F ψ h) x := by
  apply DifferentiableAt.prodMk
  · exact (hF.differentiableAt (by norm_num)).comp x hψ
  · apply differentiableAt_pi.mpr
    intro i
    have hd : DifferentiableAt ℂ (fderiv ℂ F) (ψ x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    exact (hd.clm_apply (differentiableAt_const (h i))).comp x hψ

 theorem simple_polarPair_unit {F c S : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hc : ContDiffAt ℂ 2 c (ψ x)) (hS : ContDiffAt ℂ 2 S (ψ x))
    (hψ : DifferentiableAt ℂ ψ x)
    (hFS : F =ᶠ[𝓝 (ψ x)] (fun y => c y * S y)) (hcx : c (ψ x) ≠ 0)
    (hz : polarPair F ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair F ψ h) x).IsInvertible) :
    polarPair S ψ h x = 0 ∧ (fderiv ℂ (polarPair S ψ h) x).IsInvertible := by
  let U : V → ((ℂ × (κ → ℂ)) →L[ℂ] (ℂ × (κ → ℂ))) :=
    fun y => triangularMultiplier (c (ψ y)) (fun i => fderiv ℂ c (ψ y) (h i))
  have hg := differentiableAt_polarPair (h := h) hS hψ
  have hU : DifferentiableAt ℂ U x := by
    apply differentiableAt_triangularMultiplier
    · exact (hc.differentiableAt (by norm_num)).comp x hψ
    · exact (differentiableAt_polarPair (h := h) hc hψ).snd
  have hu : (U x).IsInvertible := triangularMultiplier_invertible _ _ hcx
  have he : polarPair F ψ h =ᶠ[𝓝 x] (fun y => U y (polarPair S ψ h y)) := by
    have hlocal : ∀ᶠ z in 𝓝 (ψ x),
        (F z,fun i => fderiv ℂ F z (h i)) =
          triangularMultiplier (c z) (fun i => fderiv ℂ c z (h i))
            (S z,fun i => fderiv ℂ S z (h i)) := by
      filter_upwards [hFS, hFS.fderiv (𝕜 := ℂ), hc.eventually (by norm_num), hS.eventually (by norm_num)]
        with z h0 h1 hc' hS'
      rw [h1, fderiv_fun_mul (hc'.differentiableAt (by norm_num))
        (hS'.differentiableAt (by norm_num)), triangularMultiplier_apply]
      apply Prod.ext h0
      ext i
      simp
    exact hψ.continuousAt.eventually hlocal
  have hsz : polarPair S ψ h x = 0 := by
    apply hu.bijective.injective
    rw [map_zero, ← he.eq_of_nhds, hz]
  refine ⟨hsz, ?_⟩
  apply (simple_unit_multiplier_iff hU hg hsz hu).mp
  rwa [← he.fderiv_eq]
end PermanentBorder.PolarAnalysis

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SchurLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

omit [Fintype κ] in
 theorem kernelRemaining_solved
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (ha : DifferentiableAt ℂ a (ψ x))
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) (ψ x))
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) (ψ x))
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) (ψ x))
    (hx : (E (ψ x)).det ≠ 0) :
    kernelRemaining a β γ E ψ h
        (x, graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ) x) =
      polarPair (fun y => scalar (a y) (β y) (γ y) (E y)) ψ h x := by
  apply Prod.ext
  · simp [kernelRemaining, graphKernels, polarPair, scalar, right,
      dotProduct_neg, sub_eq_add_neg]
  · ext i
    exact (differential_scalar ha hβ hγ hE hx (h i)).symm

omit [Fintype ι] [DecidableEq ι] in
 theorem contDiff_block {a : T → ℂ} {β γ : T → ι → ℂ}
    {E : T → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (ha : ContDiff ℂ n a)
    (hβ : ∀ i, ContDiff ℂ n (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ n (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) (i j : Unit ⊕ ι) :
    ContDiff ℂ n (fun y => block (a y) (β y) (γ y) (E y) i j) := by
  cases i <;> cases j <;> simp only [block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply]
  · exact ha
  · exact hβ _
  · exact hγ _
  · exact hE _ _

omit [DecidableEq ι] in
 theorem differentiableAt_kernelRemaining
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    {w : (ι → ℂ) × (ι → ℂ)}
    (ha : ContDiff ℂ 2 a)
    (hβ : ∀ i, ContDiff ℂ 2 (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ 2 (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ 2 (fun y => E y i j))
    (hψ : DifferentiableAt ℂ ψ x) :
    DifferentiableAt ℂ (kernelRemaining a β γ E ψ h) (x,w) := by
  have hψ' : DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => ψ z.1) (x,w) :=
    hψ.comp (x,w) (ContinuousLinearMap.fst ℂ (ℂ × (κ → ℂ)) ((ι → ℂ) × (ι → ℂ))).differentiableAt
  have hnorm (j : Unit ⊕ ι) (b : Bool) :
      DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => normalized (if b then z.2.1 else z.2.2) j) (x,w) := by
    cases j <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, normalized, Sum.elim_inl,
      Sum.elim_inr] <;> fun_prop
  have hdir (i j : Unit ⊕ ι) (l : κ) :
      DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) =>
        dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h l) i j) (x,w) := by
    have hc := (contDiff_block ha hβ hγ hE i j).contDiffAt (x := ψ x)
    have hd := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    exact (hd.clm_apply (differentiableAt_const (h l))).comp (x,w) hψ'
  apply DifferentiableAt.prodMk
  · change DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => a (ψ z.1) + ∑ j, β (ψ z.1) j * z.2.1 j) (x,w)
    apply DifferentiableAt.add ((ha.differentiable (by norm_num) _).comp (x,w) hψ')
    apply DifferentiableAt.fun_sum
    intro j _
    apply DifferentiableAt.mul (((hβ j).differentiable (by norm_num) _).comp (x,w) hψ')
    fun_prop
  · apply differentiableAt_pi.mpr
    intro l
    change DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => ∑ i, normalized z.2.2 i *
      ∑ j, dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h l) i j *
        normalized z.2.1 j) (x,w)
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.mul (hnorm i false)
    apply DifferentiableAt.fun_sum
    intro j _
    exact (hdir i j l).mul (hnorm j true)

 theorem simple_kernel_lift
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (ha : ContDiff ℂ 2 a)
    (hβ : ∀ i, ContDiff ℂ 2 (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ 2 (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ 2 (fun y => E y i j))
    (hψ : DifferentiableAt ℂ ψ x) (hx : (E (ψ x)).det ≠ 0)
    (hz : polarPair (fun y => (block (a y) (β y) (γ y) (E y)).det) ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair
      (fun y => (block (a y) (β y) (γ y) (E y)).det) ψ h) x).IsInvertible) :
    let g := graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    let R := kernelRemaining a β γ E ψ h
    let J := auxiliary (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    (R (x,g x),J (x,g x)) = 0 ∧
      (fderiv ℂ (fun z => (R z,J z)) (x,g x)).IsInvertible := by
  let S := fun y => scalar (a y) (β y) (γ y) (E y)
  let g := graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
  let R := kernelRemaining a β γ E ψ h
  let J := auxiliary (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
  have hdE : ∀ i j y, DifferentiableAt ℂ (fun z => E z i j) y :=
    fun i j => (hE i j).differentiable (by norm_num)
  have hdb : ∀ i y, DifferentiableAt ℂ (fun z => β z i) y :=
    fun i => (hβ i).differentiable (by norm_num)
  have hdg : ∀ i y, DifferentiableAt ℂ (fun z => γ z i) y :=
    fun i => (hγ i).differentiable (by norm_num)
  have hda := ha.differentiable (by norm_num)
  have hevent : ∀ᶠ y in 𝓝 (ψ x), (E y).det ≠ 0 :=
    (differentiableAt_det (fun i j => hdE i j (ψ x))).continuousAt.eventually_ne hx
  have hFS : (fun y => (block (a y) (β y) (γ y) (E y)).det) =ᶠ[𝓝 (ψ x)]
      (fun y => (E y).det * S y) := by
    filter_upwards [hevent] with y hy
    exact det_block _ _ _ _ hy
  obtain ⟨hSz,hSs⟩ := simple_polarPair_unit (contDiff_det hE).contDiffAt
    (contDiffAt_scalar ha hβ hγ hE hx) hψ hFS hx hz hsimple
  have hRG : (fun y => R (y,g y)) =ᶠ[𝓝 x] polarPair S ψ h := by
    filter_upwards [hψ.continuousAt.eventually hevent] with y hy
    exact kernelRemaining_solved (hda _) (fun i => hdb i _) (fun i => hdg i _)
      (fun i j => hdE i j _) hy
  change (R (x,g x),J (x,g x)) = 0 ∧ _
  constructor
  · apply Prod.ext
    · exact hRG.eq_of_nhds.trans hSz
    · exact auxiliary_solved _ _ _ _ hx
  · apply simple_kernel_elimination (β := β ∘ ψ) (γ := γ ∘ ψ) (E := E ∘ ψ)
      (fun i => (hdb i _).comp x hψ) (fun i => (hdg i _).comp x hψ)
      (fun i j => (hdE i j _).comp x hψ) hx
      (differentiableAt_kernelRemaining ha hβ hγ hE hψ)
    rwa [hRG.fderiv_eq]
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype σ]

omit [Fintype ι] [DecidableEq ι] in
 theorem block_entries (M : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) :
    block (M (.inl ()) (.inl ())) (fun j => M (.inl ()) (.inr j))
      (fun i => M (.inr i) (.inl ())) (fun i j => M (.inr i) (.inr j)) = M := by
  ext i j
  cases i <;> cases j <;> rfl

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

 theorem exists_common_functional (v : J → I → ℂ) (hv : ∀ j, v j ≠ 0) :
    ∃ f : I → ℂ, ∀ j, f ⬝ᵥ v j ≠ 0 := by
  classical
  let p (j : J) := LinearMap.ker (dotLinear (v j))
  have hp (j : J) : p j ≠ ⊤ := by
    intro h
    apply hv j
    funext i
    have hi : Pi.single i 1 ∈ p j := h ▸ Submodule.mem_top
    change (Pi.single i 1 : I → ℂ) ⬝ᵥ v j = 0 at hi
    simpa only [single_dotProduct, one_mul, Pi.zero_apply] using hi
  obtain ⟨f,hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨f,hf⟩

 theorem det_updateRow_one (i : I) (f : I → ℂ) :
    ((1 : Matrix I I ℂ).updateRow i f).det = f i := by
  have hsum : (∑ k, f k • (1 : Matrix I I ℂ) k) = f := by
    ext j
    simp [Matrix.one_apply, Finset.sum_apply, Pi.smul_apply]
  simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using
    (Matrix.det_updateRow_sum (1 : Matrix I I ℂ) i f)

 theorem exists_common_kernel_chart (i₀ : I) (A : J → Matrix I I ℂ)
    (hA : ∀ j, (A j).adjugate ≠ 0) :
    ∃ S : Matrix I I ℂ, S.det ≠ 0 ∧
      ∀ j, ∃ r, (A j * S).adjugate i₀ r ≠ 0 := by
  classical
  have hv : ∀ j, ∃ r, (fun i => (A j).adjugate i r) ≠ 0 := by
    intro j
    by_contra! hz
    exact hA j (by funext i r; exact congrFun (hz r) i)
  choose r hr using hv
  let v : Option J → I → ℂ
    | none => Pi.single i₀ 1
    | some j => fun i => (A j).adjugate i (r j)
  have hv' : ∀ j, v j ≠ 0 := by
    rintro (_|j)
    · intro h
      have := congrFun h i₀
      simp [v] at this
    · exact hr j
  obtain ⟨f,hf⟩ := exists_common_functional v hv'
  have hf₀ : f i₀ ≠ 0 := by
    simpa only [v, dotProduct_single, mul_one] using hf none
  let T : Matrix I I ℂ := (1 : Matrix I I ℂ).updateRow i₀ f
  have hT : T.det ≠ 0 := by simpa only [T, det_updateRow_one] using hf₀
  let S : Matrix I I ℂ := T⁻¹
  have hST : S * T = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT)
  have hS : S.det ≠ 0 := by
    have he := congrArg Matrix.det hST
    rw [Matrix.det_mul, Matrix.det_one] at he
    exact left_ne_zero_of_mul_eq_one he
  have hadj : S.adjugate = S.det • T := by
    calc
      S.adjugate = S.adjugate * (S*T) := by rw [hST, Matrix.mul_one]
      _ = (S.adjugate*S)*T := (Matrix.mul_assoc _ _ _).symm
      _ = S.det • T := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨S,hS,?_⟩
  intro j
  refine ⟨r j,?_⟩
  rw [Matrix.adjugate_mul_distrib, hadj, Matrix.smul_mul]
  change S.det * (T * (A j).adjugate) i₀ (r j) ≠ 0
  apply mul_ne_zero hS
  simpa only [Matrix.mul_apply, T, Matrix.updateRow_self, v, dotProduct] using hf (some j)
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem determinantDifferential (M H : I → I → ℂ) :
    fderiv ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M H =
      ∑ i, ∑ j, (Matrix.of M).adjugate j i * H i j := by
  have hd := (determinantMultilinear (I := I)).hasFDerivAt M
  have he : fderiv ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M =
      (determinantMultilinear (I := I)).linearDeriv M := hd.fderiv
  rw [he, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((Matrix.of M).updateRow i (H i)).det = _
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose]
  change (Matrix.of M).transpose.cramer (H i) i = _
  rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
  rfl

 theorem differentiableAt_determinant (M : I → I → ℂ) :
    DifferentiableAt ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M :=
  ((determinantMultilinear (I := I)).hasFDerivAt M).differentiableAt

 theorem adjugate_ne_zero_of_differential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E → I → I → ℂ} {x : E} (hA : DifferentiableAt ℂ A x)
    (hd : fderiv ℂ (fun y => (Matrix.of (A y)).det) x ≠ 0) :
    (Matrix.of (A x)).adjugate ≠ 0 := by
  intro hz
  apply hd
  change fderiv ℂ ((fun M : I → I → ℂ => (Matrix.of M).det) ∘ A) x = 0
  rw [fderiv_comp x (differentiableAt_determinant (A x)) hA]
  ext v
  simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply]
  rw [determinantDifferential, hz]
  simp
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
open scoped Topology
variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem first_derivative_ne_zero_of_invertible
    {P : (ℂ × W) → (ℂ × W)} {x : ℂ × W}
    (hP : DifferentiableAt ℂ P x) (hs : (fderiv ℂ P x).IsInvertible) :
    fderiv ℂ (fun y => (P y).1) x ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := hs.bijective.surjective (1,0)
  have hh := congrArg (fun L : (ℂ × W) →L[ℂ] ℂ => L v) hz
  rw [(hP.hasFDerivAt.fst).fderiv] at hh
  change (fderiv ℂ P x v).1 = 0 at hh
  rw [hv] at hh
  exact one_ne_zero hh

variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

 theorem selected_simple_common_kernel_chart
    (i₀ : I) (A : E → I → I → ℂ) (ψ : (ℂ × W) → E)
    (P : (ℂ × W) → (ℂ × W)) (x : J → (ℂ × W))
    (hA : ∀ j, DifferentiableAt ℂ A (ψ (x j)))
    (hψ : ∀ j, DifferentiableAt ℂ ψ (x j))
    (hP : ∀ j, DifferentiableAt ℂ P (x j))
    (hfirst : ∀ y, (P y).1 = (Matrix.of (A (ψ y))).det)
    (hsimple : ∀ j, (fderiv ℂ P (x j)).IsInvertible) :
    ∃ S : Matrix I I ℂ, S.det ≠ 0 ∧
      ∀ j, ∃ r, (Matrix.of (A (ψ (x j))) * S).adjugate i₀ r ≠ 0 := by
  apply exists_common_kernel_chart
  intro j
  apply adjugate_ne_zero_of_differential ((hA j).comp (x j) (hψ j))
  have hn := first_derivative_ne_zero_of_invertible (hP j) (hsimple j)
  simpa only [Function.comp_apply, hfirst] using hn
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix

 theorem det_submatrix_two_equiv {I J R : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [CommRing R]
    (er ec : I ≃ J) (M : Matrix J J R) :
    (M.submatrix er ec).det = (Equiv.Perm.sign (ec.symm.trans er) : ℤ) * M.det := by
  exact Matrix.det_reindex er.symm ec.symm M

 theorem determinant_pivot_scalar {n : ℕ} (i r : Fin (n+1)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      (M.submatrix (pivotEquiv r) (pivotEquiv i)).det = c*M.det := by
  let c : ℂ := (Equiv.Perm.sign ((pivotEquiv i).symm.trans (pivotEquiv r)) : ℤ)
  refine ⟨c, ?_, fun M => det_submatrix_two_equiv _ _ _⟩
  exact Int.cast_ne_zero.mpr (Units.ne_zero _)

 theorem pivot_minor_ne_zero {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i r : Fin (n+1)) (h : M.adjugate i r ≠ 0) :
    ((M.submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr).det ≠ 0 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h
  have he : (M.submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr =
      M.submatrix r.succAbove i.succAbove := by ext a b; rfl
  rw [he]
  exact (mul_ne_zero_iff.mp h).2
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

 theorem simple_matrix_kernel_lift
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (hF : ∀ i j, ContDiff ℂ 2 (fun y => F y i j))
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (hψ : DifferentiableAt ℂ ψ x)
    (hx : ((F (ψ x)).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hz : polarPair (fun y => (F y).det) ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair (fun y => (F y).det) ψ h) x).IsInvertible) :
    matrixKernelSystem F ψ h (matrixKernelPoint F ψ x) = 0 ∧
      (fderiv ℂ (matrixKernelSystem F ψ h) (matrixKernelPoint F ψ x)).IsInvertible := by
  apply simple_kernel_lift (hF _ _) (fun j => hF _ _) (fun i => hF _ _)
    (fun i j => hF _ _) hψ hx
  · simpa only [block_entries] using hz
  · simpa only [block_entries] using hsimple
end PermanentBorder.PolarAnalysis.Schur

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.BilinearCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis
open Matrix Schur Filter
open scoped Topology
variable {κ J T : Type*} [Fintype κ] [Finite J]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

 theorem finite_simple_polar_kernel_lifts {n : ℕ}
    (i₀ : Fin (n+1)) (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hF : ∀ i j, ContDiff ℂ 2 (fun y => F y i j))
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T) (x : J → (ℂ × (κ → ℂ)))
    (hψ : ∀ j, DifferentiableAt ℂ ψ (x j))
    (hz : ∀ j, polarPair (fun y => (F y).det) ψ h (x j) = 0)
    (hsimple : ∀ j, (fderiv ℂ (polarPair (fun y => (F y).det) ψ h) (x j)).IsInvertible) :
    ∃ S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ, S.det ≠ 0 ∧ ∀ j, ∃ r : Fin (n+1),
      let F' := fun y => (F y * S).submatrix (pivotEquiv r) (pivotEquiv i₀)
      matrixKernelSystem F' ψ h (matrixKernelPoint F' ψ (x j)) = 0 ∧
        (fderiv ℂ (matrixKernelSystem F' ψ h) (matrixKernelPoint F' ψ (x j))).IsInvertible := by
  have hFd : ∀ y, DifferentiableAt ℂ (fun y i j => F y i j) y := by
    intro y
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hF i j).differentiable (by norm_num) y
  obtain ⟨S,hS,hs⟩ := selected_simple_common_kernel_chart i₀ (fun y i j => F y i j)
    ψ (polarPair (fun y => (F y).det) ψ h) x (fun j => hFd _) hψ
    (fun j => differentiableAt_polarPair (contDiff_det hF).contDiffAt (hψ j))
    (fun _ => rfl) hsimple
  refine ⟨S,hS,?_⟩
  intro j
  obtain ⟨r,hr⟩ := hs j
  refine ⟨r,?_⟩
  let F' := fun y => (F y * S).submatrix (pivotEquiv r) (pivotEquiv i₀)
  change matrixKernelSystem F' ψ h (matrixKernelPoint F' ψ (x j)) = 0 ∧ _
  have hF' : ∀ a b, ContDiff ℂ 2 (fun y => F' y a b) := by
    intro a b
    change ContDiff ℂ 2 (fun y => ∑ k, F y (pivotEquiv r a) k * S k (pivotEquiv i₀ b))
    apply ContDiff.sum
    intro k _
    exact (hF _ _).mul contDiff_const
  obtain ⟨c,hc,hcF⟩ := determinant_pivot_scalar i₀ r
  have hcs : c*S.det ≠ 0 := mul_ne_zero hc hS
  have hdet (y : T) : (F' y).det = (c*S.det)*(F y).det := by
    rw [hcF, Matrix.det_mul]
    ring
  have hrel : (fun y => (F y).det) =ᶠ[𝓝 (ψ (x j))]
      (fun y => (c*S.det)⁻¹ * (F' y).det) := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [hdet, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
  obtain ⟨hzero,hsimp⟩ := simple_polarPair_unit contDiffAt_const
    (contDiff_det hF').contDiffAt (hψ j) hrel (inv_ne_zero hcs) (hz j) (hsimple j)
  apply simple_matrix_kernel_lift F' hF' (hψ j)
    (pivot_minor_ne_zero (F (ψ (x j)) * S) i₀ r hr) hzero hsimp
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.KernelBilinear
open MvPolynomial PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
omit [Fintype κ] in
lemma base_group (i r : Fin (n+1)) (j : Groups) : (base (κ := κ) i r j).1 = j := by
  rcases j with _ | (_ | _) <;> rfl
lemma chart_base (i r : Fin (n+1)) (z : ChartSpace κ n) (j : Groups) :
    chart i r z (base i r j) = 1 := by
  rcases j with _ | (_ | _) <;> simp [chart, coordinates, base]
lemma contDiff_chart (i r : Fin (n+1)) : ContDiff ℂ 1 (chart (κ := κ) i r) := by
  apply contDiff_pi.mpr
  rintro ⟨j,t⟩
  rcases j with _ | (_ | _)
  · rcases t with _ | (_ | t) <;> simp [chart, coordinates] <;> fun_prop
  · change ContDiff ℂ 1 (fun z : ChartSpace κ n => normalized z.2.1 ((pivotEquiv i).symm t))
    cases (pivotEquiv i).symm t <;> simp [normalized] <;> fun_prop
  · change ContDiff ℂ 1 (fun z : ChartSpace κ n => normalized z.2.2 ((pivotEquiv r).symm t))
    cases (pivotEquiv r).symm t <;> simp [normalized] <;> fun_prop

lemma chart_separated {i r s : Fin (n+1)} {x y : ChartSpace κ n} (h : x.1 ≠ y.1) :
    Multigraded.BlockSeparated Sigma.fst (chart i r x) (chart i s y) := by
  have he : optionProduct.symm x.1 ≠ optionProduct.symm y.1 :=
    fun e => h (optionProduct.symm.injective e)
  obtain ⟨j,hj⟩ := Function.ne_iff.mp he
  refine ⟨⟨none,none⟩,⟨none,some j⟩,rfl,?_⟩
  simpa [chart, coordinates] using hj.symm
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}

lemma sum_norm (i : Fin (n+1)) (f : Fin (n+1) → ℂ) (z : Fin n → ℂ) :
    ∑ j, f j * norm i z j = f i + ∑ j, f (i.succAbove j) * z j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma polar_norm (i r : Fin (n+1)) (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (u v : Fin n → ℂ) :
    (∑ a, ∑ b, B a b * norm i u b * norm r v a) =
      normalized v ⬝ᵥ ((B.submatrix (pivotEquiv r) (pivotEquiv i)) *ᵥ normalized u) := by
  simp only [mulVec, dotProduct]
  symm
  apply Fintype.sum_equiv (pivotEquiv r)
  intro a
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (pivotEquiv i) _ _ (fun b => by
    simp [norm, Matrix.submatrix_apply, mul_comm, mul_left_comm])

section Bridge
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

lemma system_eq_matrixKernelSystem
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i r : Fin (n+1)) (z : ChartSpace κ n) :
    output r (fun j => eval (chart i r z) (system A₀ A B i j)) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i)) ψ h z := by
  have hright (a : Fin (n+1)) :
      eval (chart i r z) (rightEquation A₀ A a) =
        F (ψ z.1) a i + ∑ j, F (ψ z.1) a (i.succAbove j) * z.2.1 j := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_right]
    simp only [hlocal]
    exact sum_norm i _ _
  have hleft (b : Fin (n+1)) :
      eval (chart i r z) (leftEquation A₀ A b) =
        F (ψ z.1) r b + ∑ a, z.2.2 a * F (ψ z.1) (r.succAbove a) b := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_left]
    simp only [hlocal]
    rw [sum_norm]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  have hpolar (k : κ) :
      eval (chart i r z) (polarEquation (B k)) =
        normalized z.2.2 ⬝ᵥ ((B k).submatrix (pivotEquiv r) (pivotEquiv i) *ᵥ normalized z.2.1) := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_polar, polar_norm]
  have hdir' (k : κ) :
      dirMatrix (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i))
        (ψ z.1) (h k) = (B k).submatrix (pivotEquiv r) (pivotEquiv i) := by
    ext a b
    exact hdir _ _ _ _
  apply Prod.ext
  · apply Prod.ext
    · change eval (chart i r z) (rightEquation A₀ A r) = _
      rw [hright]
      rfl
    · funext k
      change eval (chart i r z) (polarEquation (B k)) = _
      rw [hpolar]
      change _ = normalized z.2.2 ⬝ᵥ (dirMatrix
        (fun y => block ((F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inl ()))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inr j))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inr j) (.inl ()))
          (((F y).submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr))
        (ψ z.1) (h k) *ᵥ normalized z.2.1)
      have hb : (fun y => block ((F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inl ()))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inr j))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inr j) (.inl ()))
          (((F y).submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr)) =
          (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i)) := by
        funext y a b
        cases a with
        | inl u => cases u; cases b with
          | inl v => cases v; rfl
          | inr b => rfl
        | inr a => cases b with
          | inl v => cases v; rfl
          | inr b => rfl
      rw [hb, hdir']
  · apply Prod.ext
    · funext j
      change eval (chart i r z) (rightEquation A₀ A (r.succAbove j)) = _
      rw [hright]
      rfl
    · funext j
      change eval (chart i r z) (leftEquation A₀ A (i.succAbove j)) = _
      rw [hleft]
      rfl
end Bridge
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ J : Type} [Fintype κ] [Fintype J] {n : ℕ}
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

theorem selected_kernel_count
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i : Fin (n+1)) (r : J → Fin (n+1)) (x : J → ChartSpace κ n)
    (hx : Function.Injective (fun j => (x j).1))
    (hz : ∀ j, matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h) (x j)).IsInvertible) :
    Fintype.card J ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  classical
  have he (j : J) :
      (fun z => output (r j) (fun a => eval (chart i (r j) z) (system A₀ A B i a))) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h := by
    funext z
    exact system_eq_matrixKernelSystem F ψ h A₀ A B hlocal hdir i (r j) z
  have hz' (j : J) (a : Equations κ n) : eval (chart i (r j) (x j)) (system A₀ A B i a) = 0 := by
    have hh : output (r j) (fun a => eval (chart i (r j) (x j)) (system A₀ A B i a)) =
        output (r j) 0 := by
      rw [map_zero, congrFun (he j) (x j)]
      exact hz j
    exact congrFun ((output (r j)).injective hh) a
  have hc := Multigraded.bilinear_simple_point_count_reindex (dimensions κ n)
    Sigma.fst variablesEquiv variablesEquiv_group firstGroup secondGroup card_equations
    (system A₀ A B i) (system_homogeneous A₀ A B i)
    (fun j => base i (r j)) (fun j => base_group i (r j))
    (fun j => output (r j)) (fun j => chart i (r j)) (fun j => contDiff_chart i (r j))
    (fun j z => chart_base i (r j) z) x
    (fun j k hjk => chart_separated (fun hh => hjk (hx hh))) hz'
    (fun j => by rw [he]; exact hs j)
  exact hc.trans mixed_coefficient_bound
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {σ κ J : Type} [Fintype σ] [Fintype κ] [Fintype J] {n : ℕ}

lemma affine_contDiff (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin (n+1)) :
    ContDiff ℂ 2 (fun y => affine A₀ A y i j) := by
  unfold affine
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

lemma affine_derivative (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y h : σ → ℂ) (i j : Fin (n+1)) :
    fderiv ℂ (fun y => affine A₀ A y i j) y h = ∑ v, h v * A v i j := by
  let L : (σ → ℂ) →L[ℂ] ℂ := ∑ v, A v i j • ContinuousLinearMap.proj v
  have he : (fun y => affine A₀ A y i j) = (fun y => A₀ i j + L y) := by
    funext y
    simp [affine,L,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_comm]
  have hd : HasFDerivAt (fun y => A₀ i j + L y) L y := by
    exact HasFDerivAt.const_add (A₀ i j) L.hasFDerivAt
  rw [he, hd.fderiv]
  simp [L,mul_comm]

lemma affine_right_mul (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :
    affine (A₀*S) (fun v => A v*S) y = affine A₀ A y * S := by
  simp [affine, add_mul, Finset.sum_mul]

theorem affine_polar_count
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (b : σ → ℂ) (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (x : J → ℂ × (κ → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    Fintype.card J ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  classical
  let ψ := fun z : ℂ × (κ → ℂ) => b + L (optionProduct.symm z)
  obtain ⟨S,hS,hr⟩ := finite_simple_polar_kernel_lifts (0 : Fin (n+1))
    (affine A₀ A) (affine_contDiff A₀ A) ψ h x
    (fun _ => ((differentiable_const b).add (L.differentiable.comp optionProduct.symm.differentiable)).differentiableAt)
    hz hs
  choose r hr using hr
  let A₀' := A₀*S
  let A' := fun v => A v*S
  let B₀ := affine A₀' A' b
  let B := fun k => ∑ v, L (Pi.single k 1) v • A' v
  let D := fun k => ∑ v, h k v • A' v
  have hlocal (z : ℂ × (κ → ℂ)) (i j : Fin (n+1)) :
      B₀ i j + ∑ k, B k i j * optionProduct.symm z k = affine A₀' A' (ψ z) i j := by
    have hexp : optionProduct.symm z = ∑ k, optionProduct.symm z k • Pi.single k 1 := by
      ext k
      simp [Pi.single_apply]
    have hLe (v : σ) : L (optionProduct.symm z) v =
        ∑ k, optionProduct.symm z k * L (Pi.single k 1) v := by
      conv_lhs => rw [hexp, map_sum]
      simp
    simp only [B₀, B, affine, ψ, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.add_apply, hLe, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm, ← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hd (y : σ → ℂ) (k : κ) (i j : Fin (n+1)) :
      fderiv ℂ (fun y => affine A₀' A' y i j) y (h k) = D k i j := by
    rw [affine_derivative]
    simp [D,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  let X := fun j => matrixKernelPoint
    (fun y => (affine A₀' A' y).submatrix (pivotEquiv (r j)) (pivotEquiv (0 : Fin (n+1)))) ψ (x j)
  apply selected_kernel_count (affine A₀' A') ψ h B₀ B D hlocal hd 0 r X
  · exact hx
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).1
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).2
end PermanentBorder.KernelBilinear

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.RegularSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

lemma linear_homogeneous (l : Option ι → R) : (linear l).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C (Option ι) (l j)).mul (isHomogeneous_X R j)

lemma pderiv_linear (l : Option ι → R) (j : Option ι) : pderiv j (linear l) = C (l j) := by
  classical
  cases j <;> simp [linear, pderiv_X, Pi.single_apply]

lemma pderiv_normalized (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (i j : Option ι) : pderiv j (normalized H l i) = square H l i j := by
  cases i <;> simp [normalized, square, pderiv_linear]

lemma det_homogeneous {σ n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ R)) (e : n → ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous (e i)) : A.det.IsHomogeneous (∑ i, e i) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ i, A (p i) i).IsHomogeneous (∑ i, e (p i)) :=
    IsHomogeneous.prod _ _ _ (fun i _ => hA _ _)
  rw [Equiv.sum_comp] at hp
  change (p.sign : ℤ) • (∏ i, A (p i) i) ∈
    (homogeneousSubmodule σ R (∑ i, e i)).restrictScalars ℤ
  exact Submodule.smul_mem _ _ hp

lemma square_det_homogeneous (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (e : ι → ℕ) (hH : ∀ i, (H i).IsHomogeneous (e i)) :
    (square H l).det.IsHomogeneous (∑ i, (e i - 1)) := by
  classical
  have h := det_homogeneous (square H l) (Option.elim' 0 (fun i => e i - 1)) (by
    intro i j
    cases i with
    | none => exact isHomogeneous_C _ _
    | some i => exact (hH i).pderiv)
  simpa using h

lemma bad_homogeneous (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (e : ι → ℕ) (hH : ∀ i, (H i).IsHomogeneous (e i)) (i : Option ι) :
    (bad H l i).IsHomogeneous (degrees e i) := by
  cases i with
  | none => exact (linear_homogeneous l).mul (square_det_homogeneous H l e hH)
  | some i => exact hH i

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

lemma good_iff_bad (H : ι → MvPolynomial (Option ι) K) (l : Option ι → K) :
    Good H l ↔ ∀ y : Option ι → K, (∀ i, eval y (bad H l i) = 0) → y = 0 := by
  classical
  constructor
  · intro hg y hy
    by_contra hn
    obtain ⟨hl,hj⟩ := hg y hn (fun i => hy (some i))
    have h := hy none
    change eval y (linear l * (square H l).det) = 0 at h
    rw [map_mul, RingHom.map_det] at h
    exact (mul_ne_zero hl hj) h
  · intro hz y hn hH
    have h : eval y (linear l * (square H l).det) ≠ 0 := by
      intro h
      exact hn (hz y (by intro i; cases i; exact h; exact hH _))
    rw [map_mul, RingHom.map_det] at h
    exact mul_ne_zero_iff.mp h

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma powers_homogeneous (e : ι → ℕ) (i : ι) : (powers e i).IsHomogeneous (e i) := by
  simpa [powers] using ((isHomogeneous_X ℂ (some i)).pow (e i)).sub
    ((isHomogeneous_X ℂ (none : Option ι)).pow (e i))

lemma powers_good (e : ι → ℕ) (he : ∀ i, 0 < e i) : Good (powers e) coordinate := by
  intro y hy hH
  have hp (i : ι) : y (some i) ^ e i = y none ^ e i := by
    simpa [powers, sub_eq_zero] using hH i
  have hn : y none ≠ 0 := by
    intro hn
    apply hy
    funext i
    cases i with
    | none => exact hn
    | some i =>
      have hh : y (some i) ^ e i = 0 := by rw [hp i, hn, zero_pow (ne_of_gt (he i))]
      exact eq_zero_of_pow_eq_zero hh
  have hs (i : ι) : y (some i) ≠ 0 := by
    intro hz
    have hh := hp i
    rw [hz, zero_pow (ne_of_gt (he i))] at hh
    exact (pow_ne_zero _ hn) hh.symm
  refine ⟨by simpa only [eval_coordinate] using hn, ?_⟩
  let A := (square (powers e) (coordinate (ι := ι))).map (eval y)
  have h0 (v : Option ι → ℂ) : A.mulVec v none = v none := by
    simp [A, square, coordinate, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hd (i : ι) (j : Option ι) : eval y (pderiv j (powers e i)) =
      (if some i = j then (e i : ℂ) * y (some i) ^ (e i - 1) else 0) -
      (if none = j then (e i : ℂ) * y none ^ (e i - 1) else 0) := by
    by_cases ha : some i = j <;> by_cases hb : none = j <;>
      simp [powers, pderiv_X, ha, hb]
  have h1 (v : Option ι → ℂ) (i : ι) :
      A.mulVec v (some i) = (e i : ℂ) * y (some i) ^ (e i - 1) * v (some i) -
        (e i : ℂ) * y none ^ (e i - 1) * v none := by
    change (∑ j, eval y (pderiv j (powers e i)) * v j) = _
    simp only [hd, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hi : Function.Injective A.mulVec := by
    change Function.Injective A.mulVecLin
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A.mulVec v = 0 at hv
    have hv0 : v none = 0 := by simpa only [h0, Pi.zero_apply] using congrFun hv none
    funext j
    cases j with
    | none => exact hv0
    | some i =>
      have hh := congrFun hv (some i)
      rw [h1, hv0, mul_zero, sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left
        (mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt (he i))) (pow_ne_zero _ (hs i)))
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

lemma card_power_roots (n : ℕ) (hn : 0 < n) : Nat.card {z : ℂ // z^n=1} = n := by
  let : NeZero n := ⟨ne_of_gt hn⟩
  let e := (rootsOfUnityEquivNthRoots ℂ n).trans
    (Equiv.subtypeEquivRight (fun _ => Polynomial.mem_nthRoots hn))
  rw [← Nat.card_congr e]
  exact Complex.card_rootsOfUnity n

lemma powers_card (e : ι → ℕ) (he : ∀ i, 0 < e i) :
    Nat.card (Roots (powers e) coordinate) = ∏ i, e i := by
  rw [Nat.card_congr (powersRootsEquiv e), Nat.card_pi]
  exact Finset.prod_congr rfl (fun i _ => card_power_roots (e i) (he i))

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

lemma hasFDerivAt_eval (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDerivative p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : polynomialDerivative (C a) x = 0 := by ext v; simp
    rw [he]
    simpa only [eval_C] using (hasFDerivAt_const (𝕜 := ℂ) a x)
  | add p q hp hq =>
    have he : polynomialDerivative (p+q) x = polynomialDerivative p x + polynomialDerivative q x := by
      ext v
      simp [add_mul, Finset.sum_add_distrib]
    have hd := (hp.add hq).congr_fderiv he.symm
    convert! hd using 1
    ext y
    simp
  | mul_X p i hp =>
    have he : polynomialDerivative (p*X i) x =
        (eval x p) • ContinuousLinearMap.proj i + (x i) • polynomialDerivative p x := by
      ext v
      simp [polynomialDerivative, pderiv_X, Pi.single_apply,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_comm, mul_left_comm, apply_ite]
    have hd := hp.mul ((ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := x))
    have hd' := hd.congr_fderiv he.symm
    convert! hd' using 1
    ext y
    simp

lemma contDiff_eval (p : MvPolynomial σ ℂ) :
    ContDiff ℂ 1 (fun x : σ → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ 1 (fun _ : σ → ℂ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℂ ℂ i)

lemma system_fderiv (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ) :
    fderiv ℂ (fun y i => eval y (P i)) x =
      ContinuousLinearMap.pi (fun i => polynomialDerivative (P i) x) :=
  (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_eval (P i) x)).fderiv

lemma system_fderiv_apply (P : σ → MvPolynomial σ ℂ) (x v : σ → ℂ) :
    fderiv ℂ (fun y i => eval y (P i)) x v = (jacobian P x).mulVec v := by
  rw [system_fderiv]
  ext i
  simp [jacobian, Matrix.mulVec, dotProduct]

lemma system_fderiv_invertible [DecidableEq σ] (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ)
    (h : (jacobian P x).det ≠ 0) :
    (fderiv ℂ (fun y i => eval y (P i)) x).IsInvertible := by
  have hu : IsUnit (jacobian P x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have he : ⇑(fderiv ℂ (fun y i => eval y (P i)) x) = (jacobian P x).mulVec :=
    funext (system_fderiv_apply P x)
  have hb : Function.Bijective (fderiv ℂ (fun y i => eval y (P i)) x) := by
    rw [he]
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩
  obtain ⟨u,hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr hb
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem localHomeomorph_restrictPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (h : IsLocalHomeomorph f) (s : Set Y) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U,hU,hE⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp h x.val
  let V : Set (f ⁻¹' s) := Subtype.val ⁻¹' U
  let e : V ≃ₜ ((U.domRestrict f) ⁻¹' s) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨V, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
  exact (hE.restrictPreimage s).comp e.isOpenEmbedding

theorem zero_projection_chart {X F P : Type*} [TopologicalSpace X]
    [TopologicalSpace F] [TopologicalSpace P] [Zero F]
    (f : X → F) (p : X → P) (x : {x : X // f x = 0})
    (e : OpenPartialHomeomorph X (F × P)) (hx : x.val ∈ e.source)
    (he : ∀ z, e z = (f z,p z)) :
    ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.domRestrict (fun z : {x : X // f x = 0} => p z)) := by
  let U : Set {x : X // f x = 0} := Subtype.val ⁻¹' e.source
  let A : Set (F × P) := {v | v.1 = 0}
  let h : U ≃ₜ ((e.source.domRestrict e) ⁻¹' A) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,by simpa [A, he] using z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,by simpa [A, he] using z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let g : A ≃ₜ P :=
    { toFun := fun v => v.val.2
      invFun := fun b => ⟨(0,b),rfl⟩
      left_inv := fun v => by apply Subtype.ext; exact Prod.ext v.property.symm rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨U, (e.open_source.preimage continuous_subtype_val).mem_nhds hx, ?_⟩
  have H := g.isOpenEmbedding.comp ((e.isOpenEmbedding_restrict.restrictPreimage A).comp
    h.isOpenEmbedding)
  convert H using 1
  funext z
  exact (congrArg Prod.snd (he z.val.val)).symm

theorem covering_card_locallyConstant {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (h : IsCoveringMap f) :
    IsLocallyConstant (fun y => Nat.card (f ⁻¹' {y})) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  obtain ⟨hd,U,hy,hU,hf,H,hH⟩ := h y
  filter_upwards [hU.mem_nhds hy] with z hz
  have he : IsEvenlyCovered f z (f ⁻¹' {y}) := ⟨hd,U,hz,hU,hf,H,hH⟩
  exact Nat.card_congr he.fiberHomeomorph.toEquiv.symm

theorem proper_localHomeomorph_card {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [PreconnectedSpace Y] {f : X → Y}
    (hp : IsProperMap f) (hl : IsLocalHomeomorph f) (y z : Y) :
    Nat.card (f ⁻¹' {y}) = Nat.card (f ⁻¹' {z}) := by
  have hfin (a : Y) : (f ⁻¹' {a}).Finite := by
    let : CompactSpace (f ⁻¹' {a}) := isCompact_iff_compactSpace.mp
      (hp.isCompact_preimage isCompact_singleton)
    let : DiscreteTopology (f ⁻¹' {a}) :=
      (localHomeomorph_restrictPreimage hl {a}).comap_discreteTopology
    exact Set.finite_coe_iff.mp finite_of_compact_of_discrete
  have hcov : IsCoveringMap f := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    exact hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun a _ => hfin a) hl.isLocalHomeomorphOn
  exact (covering_card_locallyConstant hcov).apply_eq_of_preconnectedSpace y z

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem localHomeomorphOn_restrictPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (s : Set Y)
    (h : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U,hU,hE⟩ := (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mp h x.val x.property
  let V : Set (f ⁻¹' s) := Subtype.val ⁻¹' U
  let e : V ≃ₜ ((U.domRestrict f) ⁻¹' s) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨V, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
  exact (hE.restrictPreimage s).comp e.isOpenEmbedding

theorem implicit_zero_projection_on {𝕜 P V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    (f : P × V → V) (s : Set P)
    (h : ∀ x : {x : P × V // f x = 0}, x.val.1 ∈ s → ∃ D : P × V →L[𝕜] V,
      HasStrictFDerivAt f D x.val ∧ (D ∘L ContinuousLinearMap.inr 𝕜 P V).IsInvertible) :
    IsLocalHomeomorph (s.restrictPreimage
      (fun x : {x : P × V // f x = 0} => x.val.1)) := by
  apply localHomeomorphOn_restrictPreimage
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro x hx
  obtain ⟨D,hd,hi⟩ := h x hx
  let φ := hd.implicitFunctionDataOfProdDomain hi
  exact zero_projection_chart f Prod.fst x φ.toOpenPartialHomeomorph
    φ.pt_mem_toOpenPartialHomeomorph_source φ.toOpenPartialHomeomorph_apply

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

theorem homogeneous_normalized_proper {T V : Type*} [TopologicalSpace T]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [ProperSpace V]
    (H : T → V → Prop) (hH : IsClosed {z : T × V | H z.1 z.2})
    (hsmul : ∀ t y (c : ℂ), H t y → H t (c • y))
    (L : T → V →ₗ[ℂ] ℂ) (hL : Continuous (fun z : T × V => L z.1 z.2))
    (hno : ∀ t y, H t y → L t y = 0 → y = 0) :
    IsProperMap (fun z : {z : T × V // H z.1 z.2 ∧ L z.1 z.2 = 1} => z.val.1) := by
  let S := Metric.sphere (0 : V) 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  let Q := {z : T × S // H z.1 z.2.val}
  let Z := {z : T × V // H z.1 z.2 ∧ L z.1 z.2 = 1}
  have hn (z : Q) : L z.val.1 z.val.2.val ≠ 0 := by
    intro h
    have he := hno _ _ z.property h
    have hh := z.val.2.property
    simp [S, he] at hh
  let q : Q → Z := fun z => ⟨(z.val.1,(L z.val.1 z.val.2.val)⁻¹ • z.val.2.val),
    hsmul _ _ _ z.property, by simp [map_smul, hn z]⟩
  have hq : Continuous q := by
    have hval : Continuous (fun z : Q => (z.val.1,z.val.2.val) : Q → T × V) := by fun_prop
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (((hL.comp hval).inv₀ hn).smul (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)))
  have hsurj : Function.Surjective q := by
    intro z
    have hz : z.val.2 ≠ 0 := by
      intro he
      have hh := z.property.2
      simp [he] at hh
    have hc : (‖z.val.2‖ : ℂ) ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hz)
    let y : S := ⟨(‖z.val.2‖ : ℂ)⁻¹ • z.val.2, by
      simp only [S, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)⟩
    refine ⟨⟨(z.val.1,y), hsmul _ _ _ z.property.1⟩, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change (L z.val.1 ((‖z.val.2‖ : ℂ)⁻¹ • z.val.2))⁻¹ •
      ((‖z.val.2‖ : ℂ)⁻¹ • z.val.2) = z.val.2
    simp [map_smul, z.property.2, smul_smul, hc]
  have hclosed : IsClosed {z : T × S | H z.1 z.2.val} :=
    hH.preimage (show Continuous (fun z : T × S => (z.1,z.2.val)) by fun_prop)
  have hp : IsProperMap (fun z : Q => z.val.1) :=
    isProperMap_fst_of_compactSpace.comp hclosed.isProperMap_subtypeVal
  exact isProperMap_of_comp_of_surj hq (by fun_prop) hp hsurj

end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SmoothSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

lemma homogeneous_aeval_scale {K L σ : Type*} [CommSemiring K] [CommSemiring L]
    [Algebra K L] {f : MvPolynomial σ K} {r : ℕ} (hf : f.IsHomogeneous r)
    (a : L) (x : σ → L) :
    aeval (fun i => a * x i) f = a^r * aeval x f := by
  classical
  conv_lhs => rw [← f.support_sum_monomial_coeff]
  conv_rhs => rw [← f.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hf.degree_eq_sum_deg_support hs]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

lemma normalized_eval_zero_iff (H : ι → MvPolynomial (Option ι) ℂ) (l y : Option ι → ℂ) :
    (fun i => eval y (normalized H l i)) = 0 ↔
      (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1 := by
  constructor
  · intro h
    constructor
    · intro i; exact congrFun h (some i)
    · have hh := congrFun h none
      simpa [normalized, sub_eq_zero] using hh
  · rintro ⟨hH,hl⟩
    funext i
    cases i <;> simp [normalized, hH, hl]

lemma good_derivative_invertible (H : ι → MvPolynomial (Option ι) ℂ)
    (l y : Option ι → ℂ) (h : Good H l)
    (hy : (fun i => eval y (normalized H l i)) = 0) :
    (fderiv ℂ (fun y i => eval y (normalized H l i)) y).IsInvertible := by
  have hh := (normalized_eval_zero_iff H l y).mp hy
  have hn : y ≠ 0 := by
    intro hz
    have := hh.2
    rw [eval_linear] at this
    simp [hz] at this
  have hd := (h y hn hh.1).2
  have hj : jacobian (normalized H l) y = (square H l).map (eval y) := by
    ext i j
    exact congrArg (eval y) (pderiv_normalized H l i j)
  apply system_fderiv_invertible
  rwa [hj]

lemma fderiv_parameter_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : ℂ × V → V} (hF : ContDiff ℂ 1 F) (t : ℂ) (x : V) :
    fderiv ℂ (fun x => F (t,x)) x =
      fderiv ℂ F (t,x) ∘L ContinuousLinearMap.inr ℂ ℂ V := by
  have hi : HasFDerivAt (fun x : V => (t,x)) (ContinuousLinearMap.inr ℂ ℂ V) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (𝕜 := ℂ) t x).prodMk (hasFDerivAt_id (𝕜 := ℂ) x)
  exact ((hF.differentiable (by decide) (t,x)).hasFDerivAt.comp x hi).fderiv

lemma normalized_family_proper (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (e : ι → ℕ)
    (hh : ∀ t i, (H t i).IsHomogeneous (e i))
    (hcH : ∀ i, Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (H z.1 i)))
    (hcL : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (linear (l z.1))))
    (s : Set ℂ) (hg : ∀ t ∈ s, Good (H t) (l t)) :
    IsProperMap (familyProjection H l s) := by
  let V := Option ι → ℂ
  have hval : Continuous (fun z : s × V => (z.1.val,z.2) : s × V → ℂ × V) := by fun_prop
  have hc (i : ι) : Continuous (fun z : s × V => eval z.2 (H z.1.val i)) :=
    Continuous.comp (f := fun z : s × V => (z.1.val,z.2)) (hcH i) hval
  have hci (i : ι) : IsClosed {z : s × V | eval z.2 (H z.1.val i) = 0} :=
    isClosed_eq (hc i) continuous_const
  have hclosed : IsClosed {z : s × V | ∀ i, eval z.2 (H z.1.val i) = 0} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter hci
  have hL : Continuous (fun z : s × V => linearEval (l z.1.val) z.2) := by
    simp only [linearEval_apply]
    exact Continuous.comp (f := fun z : s × V => (z.1.val,z.2)) hcL hval
  apply PermanentBorder.Polar.homogeneous_normalized_proper
    (T := s) (V := V) (fun t y => ∀ i, eval y (H t.val i) = 0) hclosed
    (L := fun t => linearEval (l t.val)) (hL := hL)
  · intro t y c hy i
    have hs := PermanentBorder.SliceParameters.homogeneous_aeval_scale (hh t.val i) c y
    have he : eval (c • y) (H t.val i) = c ^ e i * eval y (H t.val i) := by
      change eval (fun j => c * y j) (H t.val i) = _
      simpa [aeval_def] using hs
    rw [he, hy i, mul_zero]
  · intro t y hy hz
    by_contra hn
    exact (hg t.val t.property y hn hy).1 hz

lemma normalized_family_local (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ)
    (hc : ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (H z.1) (l z.1) i)))
    (s : Set ℂ) (hg : ∀ t ∈ s, Good (H t) (l t)) :
    IsLocalHomeomorph (familyProjection H l s) := by
  let V := Option ι → ℂ
  let S : ℂ × V → V := fun z i => eval z.2 (normalized (H z.1) (l z.1) i)
  let q : {z : ℂ × V // S z = 0} → ℂ := fun z => z.val.1
  let W := q ⁻¹' s
  let E : FamilyRoots H l s ≃ₜ W :=
    { toFun := fun z => ⟨⟨(z.val.1.val,z.val.2),
        (normalized_eval_zero_iff _ _ _).mpr z.property⟩,z.val.1.property⟩
      invFun := fun z => ⟨(⟨z.val.val.1,z.property⟩,z.val.val.2),
        (normalized_eval_zero_iff _ _ _).mp z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hq : IsLocalHomeomorph (s.restrictPreimage q) := by
    apply PermanentBorder.Polar.implicit_zero_projection_on (𝕜 := ℂ) S s
    intro z hz
    refine ⟨fderiv ℂ S z.val, hc.hasStrictFDerivAt (by decide), ?_⟩
    rw [← fderiv_parameter_slice hc z.val.1 z.val.2]
    exact good_derivative_invertible (H z.val.1) (l z.val.1) z.val.2
      (hg z.val.1 hz) z.property
  exact hq.comp E.isLocalHomeomorph

theorem normalized_count_constant (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (e : ι → ℕ)
    (hh : ∀ t i, (H t i).IsHomogeneous (e i))
    (hc : ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (H z.1) (l z.1) i)))
    (s : Set ℂ) [PreconnectedSpace s] (hg : ∀ t ∈ s, Good (H t) (l t))
    (a b : s) :
    Nat.card (Roots (H a.val) (l a.val)) = Nat.card (Roots (H b.val) (l b.val)) := by
  have hcH (i : ι) : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (H z.1 i)) :=
    (continuous_apply (some i)).comp hc.continuous
  have hcL : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (linear (l z.1))) := by
    have hcont : Continuous (fun z : ℂ × (Option ι → ℂ) =>
        eval z.2 (normalized (H z.1) (l z.1) none) + (1 : ℂ)) :=
      ((continuous_apply none).comp hc.continuous).add continuous_const
    convert! hcont using 1
    funext z
    simp [normalized]
  rw [← Nat.card_congr (familyFiberEquiv H l s a), ← Nat.card_congr (familyFiberEquiv H l s b)]
  exact PermanentBorder.Polar.proper_localHomeomorph_card
    (normalized_family_proper H l e hh hcH hcL s hg) (normalized_family_local H l hc s hg) a b

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma variable_power_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) (j : σ) :
    ∃ n : ℕ, (X j : MvPolynomial σ K)^n ∈ I := by
  have hx : (X j : MvPolynomial σ K) ∈ vanishingIdeal K (zeroLocus L I) := by
    intro y hy
    rw [hz y hy]
    simp
  rw [vanishingIdeal_zeroLocus_eq_radical] at hx
  exact hx

lemma monomial_mem_of_variable_powers {K σ : Type*} [CommSemiring K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (N : σ → ℕ)
    (hN : ∀ j, (X j : MvPolynomial σ K)^(N j) ∈ I)
    (s : σ →₀ ℕ) (c : K) (hs : (∑ j, N j) < s.degree) : monomial s c ∈ I := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, N j ≤ s j := by
    by_contra h
    have hle (j : σ) : s j ≤ N j := le_of_lt (not_le.mp (not_exists.mp h j))
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle j)
    have hd : s.degree = ∑ j, s j := by
      exact Finsupp.sum_fintype s (fun _ n => n) (fun _ => rfl)
    rw [hd] at hs
    exact (not_le_of_gt hs) hh
  have he : Finsupp.single j (N j) + (s - Finsupp.single j (N j)) = s :=
    add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hj)
  rw [← he, monomial_single_add]
  exact I.mul_mem_right _ (hN j)

theorem homogeneous_piece_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ D : ℕ, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by
  classical
  choose N hN using variable_power_certificate I hz
  refine ⟨(∑ j, N j)+1, ?_⟩
  intro f hf
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro s hs
  apply monomial_mem_of_variable_powers I N hN
  have hd : s.degree = (∑ j, N j)+1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  omega

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma intWeight_homogeneous {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f.IsHomogeneous d := by
  intro s hs
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) s = d
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast (intWeight_degree s ▸ hf hs)

lemma homogeneous_ext_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f g : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (hg : g.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (h : ∀ s : DegreeIndex σ d, f.coeff s.val = g.coeff s.val) : f = g := by
  rw [homogeneous_sum_degree hf, homogeneous_sum_degree hg]
  exact Finset.sum_congr rfl (fun s _ => congrArg (monomial s.val) (h s))

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

lemma coeff_macaulayCombination (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) (s : DegreeIndex σ D) :
    (macaulayCombination e F D b).coeff s.val = (macaulayMatrix e F D).mulVec b s := by
  classical
  simp only [macaulayCombination, coeff_sum, coeff_smul, smul_eq_mul,
    macaulayMatrix, Matrix.mulVec, dotProduct, mul_comm]

lemma macaulayCombination_mem (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    macaulayCombination e F D b ∈ Ideal.span (Set.range F) := by
  apply Ideal.sum_mem
  intro t _
  exact Submodule.smul_mem ((Ideal.span (Set.range F)).restrictScalars K) _
    (Ideal.mul_mem_right _ _ Ideal.mem_span_range_self)

lemma macaulayCombination_homogeneous (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    (macaulayCombination e F D b).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D := by
  apply IsWeightedHomogeneous.sum
  intro t _
  apply (weightedHomogeneousSubmodule K (fun _ : σ => (1 : ℤ)) D).smul_mem
  have hm : (monomial t.2.val (1 : K)).IsWeightedHomogeneous
      (fun _ : σ => (1 : ℤ)) (D-e t.1) :=
    isWeightedHomogeneous_monomial _ _ _ ((intWeight_degree t.2.val).trans t.2.property)
  rw [mem_weightedHomogeneousSubmodule]
  simpa only [add_sub_cancel] using (hF t.1).mul hm

omit [Finite σ] [Fintype ι] in
lemma macaulayMatrix_map {L : Type*} [CommRing L] (φ : K →+* L)
    (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ) :
    macaulayMatrix e (fun i => map φ (F i)) D = (macaulayMatrix e F D).map φ := by
  classical
  ext s t
  change (map φ (F t.1) * monomial t.2.val 1).coeff s.val =
    φ ((F t.1 * monomial t.2.val 1).coeff s.val)
  rw [← coeff_map, map_mul, map_monomial, φ.map_one]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

theorem macaulay_surjective_iff (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ) :
    Function.Surjective (macaulayMatrix e F D).mulVec ↔
      ∀ f : MvPolynomial σ K,
        f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D →
          f ∈ Ideal.span (Set.range F) := by
  classical
  constructor
  · intro hs f hf
    obtain ⟨b,hb⟩ := hs (fun s => f.coeff s.val)
    have he : macaulayCombination e F D b = f := by
      apply homogeneous_ext_degree (macaulayCombination_homogeneous e F hF D b) hf
      intro s
      rw [coeff_macaulayCombination, hb]
    rw [← he]
    exact macaulayCombination_mem e F D b
  · intro hs b
    let f := ∑ t : DegreeIndex σ D, monomial t.val (b t)
    have hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D :=
      sum_degree_homogeneous D b
    obtain ⟨g,hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs f hf)
    let g' := fun i => weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) (D-e i) (g i)
    have hg'h (i : ι) : (g' i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (D-e i) :=
      weightedHomogeneousComponent_mem _ _ _
    have he : ∑ i, F i * g' i = f := by
      simp_rw [g', ← PermanentBorder.Multigraded.project_mul _ (hF _)]
      rw [← map_sum]
      simp_rw [mul_comm (F _) _]
      rw [hg, weightedHomogeneousComponent_eq_self hf]
    let c : (Σ i : ι, DegreeIndex σ (D-e i)) → K := fun t => (g' t.1).coeff t.2.val
    have hc : macaulayCombination e F D c = f := by
      rw [macaulayCombination, Fintype.sum_sigma]
      rw [← he]
      apply Finset.sum_congr rfl
      intro i _
      rw [homogeneous_sum_degree (hg'h i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      change (g' i).coeff s.val • (F i * monomial s.val 1) =
        F i * monomial s.val ((g' i).coeff s.val)
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    refine ⟨c, ?_⟩
    ext s
    rw [← coeff_macaulayCombination, hc]
    exact coeff_sum_degree D b s

end Surjectivity
end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SliceCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma homogeneous_piece_certificate_all {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ N : ℕ, ∀ D ≥ N, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by
  classical
  choose M hM using variable_power_certificate I hz
  refine ⟨(∑ j, M j)+1, ?_⟩
  intro D hD f hf
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro s hs
  apply monomial_mem_of_variable_powers I M hM
  have hd : s.degree = D := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  omega

lemma macaulay_surjective_zero {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι]
    (F : ι → MvPolynomial σ K) (e : ι → ℕ) (hh : ∀ i, (F i).IsHomogeneous (e i))
    (D : ℕ) (hM : Function.Surjective (macaulayMatrix (fun i => (e i : ℤ)) F D).mulVec)
    (y : σ → K) (hy : ∀ i, eval y (F i) = 0) : y = 0 := by
  have hI : Ideal.span (Set.range F) ≤ RingHom.ker (eval y) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hy i
  have h := (macaulay_surjective_iff _ _ (fun i => homogeneous_intWeight (hh i)) D).mp hM
  funext j
  have hm : (X j : MvPolynomial σ K)^D ∈ Ideal.span (Set.range F) := by
    apply h
    apply homogeneous_intWeight
    simpa using (isHomogeneous_X K j).pow D
  have he := hI hm
  change eval y ((X j)^D) = 0 at he
  rw [map_pow, eval_X] at he
  exact eq_zero_of_pow_eq_zero he

end PermanentBorder.SliceParameters
namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma good_certificate_all (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (hh : ∀ i, (H i).IsHomogeneous (e i)) (hg : Good H l) :
    ∃ N : ℕ, ∀ D ≥ N, Function.Surjective
      (macaulayMatrix (fun i => (degrees e i : ℤ)) (bad H l) D).mulVec := by
  have hz : ∀ y ∈ zeroLocus ℂ (Ideal.span (Set.range (bad H l))), y = 0 := by
    intro y hy
    apply (good_iff_bad H l).mp hg y
    intro i
    exact hy _ Ideal.mem_span_range_self
  obtain ⟨N,hN⟩ := homogeneous_piece_certificate_all (Ideal.span (Set.range (bad H l))) hz
  refine ⟨N, fun D hD => ?_⟩
  apply (macaulay_surjective_iff _ _
    (fun i => homogeneous_intWeight (bad_homogeneous H l e hh i)) D).mpr
  intro f hf
  exact hN D hD f (intWeight_homogeneous hf)

lemma good_of_certificate (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (hh : ∀ i, (H i).IsHomogeneous (e i)) (D : ℕ)
    (hM : Function.Surjective (macaulayMatrix (fun i => (degrees e i : ℤ)) (bad H l) D).mulVec) :
    Good H l := by
  apply (good_iff_bad H l).mpr
  exact macaulay_surjective_zero (bad H l) (degrees e) (bad_homogeneous H l e hh) D hM

end PermanentBorder.CI

namespace PermanentBorder.CI
open Polynomial Matrix
open scoped Classical

lemma matrix_right_inverse {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (A : Matrix α β K) (hA : Function.Surjective A.mulVec) :
    ∃ B : Matrix β α K, A * B = 1 := by
  choose b hb using fun i : α => hA (Pi.single i 1)
  refine ⟨fun j i => b i j, ?_⟩
  ext i j
  change (A.mulVec (b j)) i = (1 : Matrix α α K) i j
  rw [hb]
  simp [Matrix.one_apply, Pi.single_apply]

lemma rank_curve {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (A : Matrix α β K[X])
    (h0 : Function.Surjective (A.map (evalRingHom (0 : K))).mulVec)
    (h1 : Function.Surjective (A.map (evalRingHom (1 : K))).mulVec) :
    ∃ q : K[X], q.eval 0 = 1 ∧ q.eval 1 = 1 ∧
      ∀ t : K, q.eval t ≠ 0 → Function.Surjective (A.map (evalRingHom t)).mulVec := by
  obtain ⟨b0,hb0⟩ := matrix_right_inverse _ h0
  obtain ⟨b1,hb1⟩ := matrix_right_inverse _ h1
  let B : Matrix β α K[X] := fun i j => C (b0 i j) + X * (C (b1 i j) - C (b0 i j))
  have hB0 : B.map (evalRingHom (0 : K)) = b0 := by
    ext i j
    change (C (b0 i j) + X * (C (b1 i j) - C (b0 i j))).eval _ = _
    simp
  have hB1 : B.map (evalRingHom (1 : K)) = b1 := by
    ext i j
    change (C (b0 i j) + X * (C (b1 i j) - C (b0 i j))).eval _ = _
    simp
  refine ⟨(A*B).det, ?_, ?_, ?_⟩
  · rw [show ((A*B).det).eval 0 = ((A*B).map (evalRingHom (0 : K))).det from
      (evalRingHom (0 : K)).map_det (A*B)]
    rw [Matrix.map_mul, hB0, hb0, Matrix.det_one]
  · rw [show ((A*B).det).eval 1 = ((A*B).map (evalRingHom (1 : K))).det from
      (evalRingHom (1 : K)).map_det (A*B)]
    rw [Matrix.map_mul, hB1, hb1, Matrix.det_one]
  · intro t ht
    have hu : IsUnit ((A*B).map (evalRingHom t)) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      apply isUnit_iff_ne_zero.mpr
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ht
    have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
    intro v
    obtain ⟨x,hx⟩ := hs v
    refine ⟨(B.map (evalRingHom t)).mulVec x, ?_⟩
    rw [Matrix.mulVec_mulVec]
    simpa only [Matrix.map_mul] using hx

lemma polynomial_nonzero_preconnected (q : ℂ[X]) (hq : q ≠ 0) :
    IsPreconnected {t : ℂ | q.eval t ≠ 0} := by
  have hs : {t : ℂ | q.eval t = 0}.Finite := q.finite_setOfPred_isRoot hq
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  exact (hs.countable.isPathConnected_compl_of_one_lt_rank hdim).isConnected.isPreconnected

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma map_linear {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (l : Option ι → R) : map φ (linear l) = linear (fun j => φ (l j)) := by
  simp [linear]

omit [Fintype ι] in
lemma map_square {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    (square H l).map (map φ) = square (fun i => map φ (H i)) (fun j => φ (l j)) := by
  ext i j
  cases i <;> simp [square, pderiv_map]

lemma map_bad {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) (i : Option ι) :
    map φ (bad H l i) = bad (fun i => map φ (H i)) (fun j => φ (l j)) i := by
  cases i with
  | none => simp only [bad, Option.elim'_none, map_mul, RingHom.map_det, RingHom.mapMatrix_apply, map_linear, map_square]
  | some i => rfl

omit [Fintype ι] in
lemma Hline_map (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (t : ℂ) (i : ι) :
    map (Polynomial.evalRingHom t) (Hline H0 H1 i) = Htime H0 H1 t i := by
  have hh : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext x; simp
  simp [Hline, Htime, map_map, hh, MvPolynomial.map_id]
omit [Fintype ι] in
lemma lline_eval (l0 l1 : Option ι → ℂ) (t : ℂ) (j : Option ι) :
    (lline l0 l1 j).eval t = ltime l0 l1 t j := by simp [lline, ltime]

omit [Fintype ι] in
lemma Htime_homogeneous (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (e : ι → ℕ)
    (h0 : ∀ i, (H0 i).IsHomogeneous (e i)) (h1 : ∀ i, (H1 i).IsHomogeneous (e i))
    (t : ℂ) (i : ι) : (Htime H0 H1 t i).IsHomogeneous (e i) := by
  apply (h0 i).add
  simpa using (isHomogeneous_C (Option ι) t).mul ((h1 i).sub (h0 i))

lemma good_curve (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (l0 l1 : Option ι → ℂ)
    (e : ι → ℕ) (h0 : ∀ i, (H0 i).IsHomogeneous (e i))
    (h1 : ∀ i, (H1 i).IsHomogeneous (e i)) (hg0 : Good H0 l0) (hg1 : Good H1 l1) :
    ∃ q : Polynomial ℂ, q.eval 0 = 1 ∧ q.eval 1 = 1 ∧
      ∀ t, q.eval t ≠ 0 → Good (Htime H0 H1 t) (ltime l0 l1 t) := by
  obtain ⟨N0,hN0⟩ := good_certificate_all H0 l0 e h0 hg0
  obtain ⟨N1,hN1⟩ := good_certificate_all H1 l1 e h1 hg1
  let D := max N0 N1
  let A := macaulayMatrix (fun i => (degrees e i : ℤ)) (bad (Hline H0 H1) (lline l0 l1)) D
  have hA (t : ℂ) : A.map (Polynomial.evalRingHom t) =
      macaulayMatrix (fun i => (degrees e i : ℤ)) (bad (Htime H0 H1 t) (ltime l0 l1 t)) D := by
    rw [← macaulayMatrix_map]
    congr 1
    funext i
    rw [map_bad]
    congr 2
    · exact funext (Hline_map H0 H1 t)
    · exact funext (lline_eval l0 l1 t)
  have ha0 : Function.Surjective (A.map (Polynomial.evalRingHom (0 : ℂ))).mulVec := by
    rw [hA]; simp only [Htime_zero, ltime_zero]
    exact hN0 D (le_max_left _ _)
  have ha1 : Function.Surjective (A.map (Polynomial.evalRingHom (1 : ℂ))).mulVec := by
    rw [hA]; simp only [Htime_one, ltime_one]
    exact hN1 D (le_max_right _ _)
  obtain ⟨q,hq0,hq1,hq⟩ := rank_curve A ha0 ha1
  refine ⟨q,hq0,hq1,fun t ht => ?_⟩
  apply good_of_certificate _ _ e (Htime_homogeneous H0 H1 e h0 h1 t) D
  rw [← hA]
  exact hq t ht

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma linear_ltime (l0 l1 : Option ι → ℂ) (t : ℂ) :
    linear (ltime l0 l1 t) = linear l0 + C t * (linear l1 - linear l0) := by
  simp only [linear, ltime, map_add, map_mul, map_sub, add_mul, mul_sub, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_assoc]

lemma normalized_time (H0 H1 : ι → MvPolynomial (Option ι) ℂ)
    (l0 l1 : Option ι → ℂ) (t : ℂ) (i : Option ι) :
    normalized (Htime H0 H1 t) (ltime l0 l1 t) i =
      normalized H0 l0 i + C t * (normalized H1 l1 i - normalized H0 l0 i) := by
  cases i with
  | none => simp only [normalized, Option.elim'_none, linear_ltime]; ring
  | some i => rfl

lemma contDiff_normalized_time (H0 H1 : ι → MvPolynomial (Option ι) ℂ)
    (l0 l1 : Option ι → ℂ) :
    ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (Htime H0 H1 z.1) (ltime l0 l1 z.1) i)) := by
  apply contDiff_pi.mpr
  intro i
  simp only [normalized_time, map_add, map_mul, map_sub, eval_C]
  exact ((contDiff_eval (normalized H0 l0 i)).comp contDiff_snd).add
    (contDiff_fst.mul (((contDiff_eval (normalized H1 l1 i)).comp contDiff_snd).sub
      ((contDiff_eval (normalized H0 l0 i)).comp contDiff_snd)))

theorem good_card (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (hh : ∀ i, (H i).IsHomogeneous (e i))
    (hg : Good H l) : Nat.card (Roots H l) = ∏ i, e i := by
  obtain ⟨q,hq0,hq1,hq⟩ := good_curve H (powers e) l coordinate e hh
    (powers_homogeneous e) hg (powers_good e he)
  have hqn : q ≠ 0 := by intro hz; simp [hz] at hq0
  let s : Set ℂ := {t | q.eval t ≠ 0}
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp
    (polynomial_nonzero_preconnected q hqn)
  let a : s := ⟨0,by simp [s,hq0]⟩
  let b : s := ⟨1,by simp [s,hq1]⟩
  have hc := normalized_count_constant (Htime H (powers e)) (ltime l coordinate) e
    (Htime_homogeneous H (powers e) e hh (powers_homogeneous e))
    (contDiff_normalized_time H (powers e) l coordinate) s hq a b
  simpa only [a,b,Htime_zero,Htime_one,ltime_zero,ltime_one,powers_card e he] using hc

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

lemma extendDerivation_algebraMap [Algebra.FormallyEtale R L]
    (D : Derivation K R L) (x : R) :
    extendDerivation D (algebraMap R L x) = D x := by
  simp [extendDerivation, LinearMap.compDer,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

lemma parameterDerivation_parameter [DecidableEq ι] (i j : ι) :
    parameterDerivation K ι i (genericParameter K ι j) = if i = j then 1 else 0 := by
  classical
  simp [parameterDerivation, genericParameter, extendDerivation_algebraMap, Pi.single_apply,
    eq_comm]

end Generic

section ChainRule
variable {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]

lemma derivation_aeval (D : Derivation K L L) (x : σ → L) (f : MvPolynomial σ K) :
    D (aeval x f) = ∑ j, aeval x (pderiv j f) * D (x j) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hf,
      map_add, pderiv_X]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp [Pi.single_apply, mul_comm]

end ChainRule
end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.GenericPolars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.Polar
open MvPolynomial

section Parametric
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma derivation_polarValue (D : Derivation K L L) (w : τ → σ → L)
    (f : MvPolynomial σ K) (y : σ → L) (i : τ) :
    D (polarValue w f y i) = (∑ j, D (w i j) * aeval y (pderiv j f)) +
      ∑ j, polarGradient w f y i j * D (y j) := by
  simp only [polarValue, map_sum, Derivation.leibniz, smul_eq_mul, derivation_aeval,
    Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · simp only [polarGradient, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

lemma polar_rows_independent_of_derivations [DecidableEq τ] [DecidableEq σ]
    (w : τ → σ → L) (f : MvPolynomial σ K) (y : σ → L)
    (D : τ × σ → Derivation K L L)
    (hw : ∀ a b i j, D (a,b) (w i j) = if (a,b) = (i,j) then 1 else 0)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (c : L) (cfs : τ → L)
    (hdep : ∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j = 0) :
    c = 0 ∧ cfs = 0 := by
  obtain ⟨b,hb⟩ := hg
  have hf' (a : τ) : ∑ j, aeval y (pderiv j f) * D (a,b) (y j) = 0 := by
    rw [← derivation_aeval, hf, map_zero]
  have hp' (a i : τ) : (if a = i then aeval y (pderiv b f) else 0) +
      ∑ j, polarGradient w f y i j * D (a,b) (y j) = 0 := by
    have hd := congrArg (D (a,b)) (hp i)
    rw [derivation_polarValue, map_zero] at hd
    convert hd using 1
    by_cases ha : a = i
    · simp [hw, ha]
    · simp [hw, ha]
  have hcfs : ∀ a, cfs a = 0 := by
    intro a
    have hs : ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
      have hh : c * (∑ j, aeval y (pderiv j f) * D (a,b) (y j)) +
          ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
        calc
          _ = ∑ j, (c * aeval y (pderiv j f) +
              ∑ i, cfs i * polarGradient w f y i j) * D (a,b) (y j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
              add_mul, mul_assoc]
            rw [Finset.sum_comm]
          _ = 0 := by simp [hdep]
      simpa only [hf', mul_zero, zero_add] using hh
    have hh : ∑ i, cfs i * ((if a = i then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
      simp only [hp', mul_zero, Finset.sum_const_zero]
    have : cfs a * aeval y (pderiv b f) = 0 := by
      simpa [mul_add, Finset.sum_add_distrib, hs] using hh
    exact (mul_eq_zero.mp this).resolve_right hb
  have hc : c = 0 := by
    have hh := hdep b
    simp only [hcfs, zero_mul, Finset.sum_const_zero, add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hb
  exact ⟨hc,funext hcfs⟩

lemma rows_independent_of_derivations [DecidableEq τ] [DecidableEq σ]
    (w : τ → σ → L) (l : σ → L) (f : MvPolynomial σ K) (y : σ → L)
    (D : Option τ × σ → Derivation K L L)
    (hw : ∀ a b i j, D (a,b) (w i j) = if (a,b) = (some i,j) then 1 else 0)
    (hl : ∀ a b j, D (a,b) (l j) = if (a,b) = (none,j) then 1 else 0)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hn : ∑ j, l j * y j = 0 ∨ ∑ j, l j * y j = 1)
    (hy : ∃ j, y j ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (c z : L) (cfs : τ → L)
    (hdep : ∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) :
    c = 0 ∧ z = 0 ∧ cfs = 0 := by
  have hf' (a : Option τ) (b : σ) :
      ∑ j, aeval y (pderiv j f) * D (a,b) (y j) = 0 := by
    rw [← derivation_aeval, hf, map_zero]
  have hp' (a : Option τ) (b : σ) (i : τ) :
      (if a = some i then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y i j * D (a,b) (y j) = 0 := by
    have hd := congrArg (D (a,b)) (hp i)
    rw [derivation_polarValue, map_zero] at hd
    convert hd using 1
    by_cases ha : a = some i
    · simp [hw, ha]
    · simp [hw, ha]
  have hl' (a : Option τ) (b : σ) :
      (if a = none then y b else 0) + ∑ j, l j * D (a,b) (y j) = 0 := by
    have hd : D (a,b) (∑ j, l j * y j) = 0 := by
      rcases hn with h | h <;> simp [h]
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, hl,
      Finset.sum_add_distrib] at hd
    by_cases ha : a = none
    · simpa [ha, add_comm] using hd
    · simpa [ha] using hd
  have combine (a : Option τ) (b : σ) :
      c * (∑ j, aeval y (pderiv j f) * D (a,b) (y j)) +
        ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) +
          z * (∑ j, l j * D (a,b) (y j)) = 0 := by
    calc
      _ = ∑ j, (c * aeval y (pderiv j f) +
          ∑ i, cfs i * polarGradient w f y i j + z * l j) * D (a,b) (y j) := by
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, add_mul, mul_assoc]
        rw [Finset.sum_comm]
      _ = 0 := by simp [hdep]
  obtain ⟨b,hyb⟩ := hy
  have hz : z = 0 := by
    have hc := combine none b
    have hpp (i : τ) : ∑ j, polarGradient w f y i j * D (none,b) (y j) = 0 := by
      simpa using hp' none b i
    simp only [hf', hpp, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at hc
    have hll := hl' none b
    simp only [ite_true] at hll
    have : z * y b = 0 := by linear_combination z * hll - hc
    exact (mul_eq_zero.mp this).resolve_right hyb
  obtain ⟨b,hgb⟩ := hg
  have hcfs : ∀ i, cfs i = 0 := by
    intro i
    have hc := combine (some i) b
    simp only [hf', mul_zero, zero_add, hz, zero_mul, add_zero] at hc
    have hs : ∑ a, cfs a * ((if some i = some a then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y a j * D (some i,b) (y j)) = 0 := by
      simp only [hp', mul_zero, Finset.sum_const_zero]
    have : cfs i * aeval y (pderiv b f) = 0 := by
      simpa [mul_add, Finset.sum_add_distrib, hc] using hs
    exact (mul_eq_zero.mp this).resolve_right hgb
  have hc : c = 0 := by
    have hd := hdep b
    simp only [hz, zero_mul, hcfs, Finset.sum_const_zero, add_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_right hgb
  exact ⟨hc,hz,funext hcfs⟩

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]

lemma square_isUnit_of_independent [DecidableEq τ]
    (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L)
    (h : ∀ (c z : L) (cfs : τ → L), (∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) →
      c = 0 ∧ z = 0 ∧ cfs = 0) : IsUnit (squareJacobian w l f y) := by
  apply Matrix.vecMul_injective_iff_isUnit.mp
  apply (squareJacobian w l f y).vecMulLinear.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨hc,hz,hs⟩ := h (v none) (v (some none)) (fun i => v (some (some i))) (by
    intro j
    have hh := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, squareJacobian, Fintype.sum_option, add_assoc,
      add_comm, add_left_comm] using hh)
  funext i
  rcases i with _ | (_ | i)
  · exact hc
  · exact hz
  · exact congrFun hs i

lemma euler_aeval {σ : Type*} [Fintype σ] {f : MvPolynomial σ K} {r : ℕ}
    (hf : f.IsHomogeneous r) (y : σ → L) :
    ∑ j, aeval y (pderiv j f) * y j = (r : L) * aeval y f := by
  classical
  have h := congrArg (aeval y) hf.sum_X_mul_pderiv
  simpa [map_sum, mul_comm] using h

lemma polar_euler_aeval (w : τ → PolarVars τ → L)
    {f : MvPolynomial (PolarVars τ) K} {r : ℕ} (hf : f.IsHomogeneous r)
    (y : PolarVars τ → L) (i : τ) :
    ∑ j, polarGradient w f y i j * y j = ((r-1 : ℕ) : L) * polarValue w f y i := by
  classical
  simp only [polarGradient, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, euler_aeval hf.pderiv]
  simp only [polarValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma square_mulVec_zero (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    {f : MvPolynomial (PolarVars τ) K} {r : ℕ} (hhom : f.IsHomogeneous r)
    (y : PolarVars τ → L) (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hl : ∑ j, l j * y j = 0) : (squareJacobian w l f y).mulVec y = 0 := by
  classical
  funext i
  rcases i with _ | (_ | i)
  · simpa [Matrix.mulVec, dotProduct, squareJacobian, hf] using euler_aeval hhom y
  · exact hl
  · simpa [Matrix.mulVec, dotProduct, squareJacobian, hp] using polar_euler_aeval w hhom y i

end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

lemma generic_no_infinity (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (hn : ∑ j, genericLinear j * y j = 0) : y = 0 := by
  classical
  by_contra hy
  have hyy : ∃ j, y j ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using hy
  have hu : IsUnit (squareJacobian genericDirections genericLinear f y) :=
    square_isUnit_of_independent _ _ _ _ (fun c z cfs hdep =>
      rows_independent_of_derivations _ _ _ _ (parameterDerivation K P)
        (by intros; exact parameterDerivation_parameter K P _ _)
        (by intros; exact parameterDerivation_parameter K P _ _)
        hf hp (Or.inl hn) hyy hg c z cfs hdep)
  have hh := square_mulVec_zero genericDirections genericLinear hhom y hf hp hn
  apply hy
  exact Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa using hh)

lemma generic_square_isUnit (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hy : y ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0) :
    IsUnit (squareJacobian genericDirections genericLinear f y) := by
  classical
  have hn : ∑ j, genericLinear j * y j ≠ 0 := fun h =>
    hy (generic_no_infinity f hhom y hf hp hg h)
  apply square_isUnit_of_independent
  intro c z cfs hdep
  have hz : z = 0 := by
    have hs : ∑ j, (c * aeval y (pderiv j f) +
        ∑ i, cfs i * polarGradient genericDirections f y i j + z * genericLinear j) * y j = 0 := by
      simp [hdep]
    have he : c * (∑ j, aeval y (pderiv j f) * y j) +
        ∑ i, cfs i * (∑ j, polarGradient genericDirections f y i j * y j) +
        z * (∑ j, genericLinear j * y j) = 0 := by
      convert hs using 1
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
        add_mul, mul_assoc]
      rw [Finset.sum_comm]
    simp only [euler_aeval hhom, polar_euler_aeval _ hhom, hf, hp,
      mul_zero, Finset.sum_const_zero, zero_add] at he
    exact (mul_eq_zero.mp he).resolve_right hn
  obtain ⟨hc,hcfs⟩ := polar_rows_independent_of_derivations genericDirections f y
    (fun (a,b) => parameterDerivation K P (some a,b))
    (by intros; simp only [genericDirections, parameterDerivation_parameter,
      Prod.mk.injEq, Option.some.injEq]) hf hp hg c cfs (by simpa [hz] using hdep)
  exact ⟨hc,hz,hcfs⟩

end GenericSquare
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Polynomials
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma polarPolynomial_homogeneous (w : τ → σ → R) {f : MvPolynomial σ R} {r : ℕ}
    (hf : f.IsHomogeneous r) (i : τ) : (polarPolynomial w f i).IsHomogeneous (r-1) := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C σ (w i j)).mul hf.pderiv

omit [Fintype τ] in
lemma linearPolynomial_homogeneous (l : σ → R) : (linearPolynomial l).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C σ (l j)).mul (isHomogeneous_X R j)

omit [Fintype σ] in
lemma det_row_homogeneous {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ R)) (e : n → ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous (e i)) : A.det.IsHomogeneous (∑ i, e i) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ i, A (p i) i).IsHomogeneous (∑ i, e (p i)) :=
    IsHomogeneous.prod _ _ _ (fun i _ => hA _ _)
  rw [Equiv.sum_comp] at hp
  change (p.sign : ℤ) • (∏ i, A (p i) i) ∈
    (homogeneousSubmodule σ R (∑ i, e i)).restrictScalars ℤ
  exact Submodule.smul_mem _ _ hp

lemma squarePolynomial_homogeneous [DecidableEq τ] (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    {f : MvPolynomial (PolarVars τ) R} {r : ℕ} (hf : f.IsHomogeneous r) :
    (squarePolynomial w l f).det.IsHomogeneous (∑ i, squareDegrees τ r i) := by
  classical
  apply det_row_homogeneous
  intro i j
  rcases i with _ | (_ | i)
  · exact hf.pderiv
  · exact isHomogeneous_C _ _
  · exact (polarPolynomial_homogeneous w hf i).pderiv

lemma badPolarSystem_homogeneous (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    {f : MvPolynomial (PolarVars τ) R} {r : ℕ} (hf : f.IsHomogeneous r) (i : PolarVars τ) :
    (badPolarSystem w l f i).IsHomogeneous (badPolarDegrees τ r i) := by
  classical
  rcases i with _ | (_ | i)
  · exact hf
  · exact (linearPolynomial_homogeneous l).mul (squarePolynomial_homogeneous w l hf)
  · exact polarPolynomial_homogeneous w hf i

end Polynomials

section Evaluation
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma eval_polarPolynomial (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) :
    eval y (polarPolynomial w (map (algebraMap K L) f) i) = polarValue w f y i := by
  simp [polarPolynomial, polarValue, pderiv_map, eval_map, aeval_def]

lemma eval_linearPolynomial (l : σ → L) (y : σ → L) :
    eval y (linearPolynomial l) = ∑ j, l j * y j := by
  simp [linearPolynomial]

lemma eval_squarePolynomial (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L) :
    (squarePolynomial w l (map (algebraMap K L) f)).map (eval y) = squareJacobian w l f y := by
  classical
  ext i j
  rcases i with _ | (_ | i)
  · simp [squarePolynomial, squareJacobian, pderiv_map, eval_map, aeval_def]
  · simp [squarePolynomial, squareJacobian]
  · simp [squarePolynomial, squareJacobian, polarPolynomial, polarGradient, pderiv_map,
      eval_map, aeval_def]

end Evaluation
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Map
variable {R S σ τ : Type*} [CommRing R] [CommRing S] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma map_polarPolynomial (φ : R →+* S) (w : τ → σ → R) (f : MvPolynomial σ R) (i : τ) :
    map φ (polarPolynomial w f i) = polarPolynomial (fun i j => φ (w i j)) (map φ f) i := by
  simp [polarPolynomial, pderiv_map]

lemma map_linearPolynomial (φ : R →+* S) (l : σ → R) :
    map φ (linearPolynomial l) = linearPolynomial (fun j => φ (l j)) := by
  simp [linearPolynomial]

lemma map_squarePolynomial (φ : R →+* S) (w : τ → PolarVars τ → R)
    (l : PolarVars τ → R) (f : MvPolynomial (PolarVars τ) R) :
    (squarePolynomial w l f).map (map φ) =
      squarePolynomial (fun i j => φ (w i j)) (fun j => φ (l j)) (map φ f) := by
  classical
  funext i j
  rcases i with _ | (_ | i)
  · simp [squarePolynomial, pderiv_map]
  · simp [squarePolynomial]
  · simp only [Matrix.map_apply, squarePolynomial, ← pderiv_map, map_polarPolynomial]

lemma map_badPolarSystem (φ : R →+* S) (w : τ → PolarVars τ → R)
    (l : PolarVars τ → R) (f : MvPolynomial (PolarVars τ) R) (i : PolarVars τ) :
    map φ (badPolarSystem w l f i) =
      badPolarSystem (fun i j => φ (w i j)) (fun j => φ (l j)) (map φ f) i := by
  classical
  rcases i with _ | (_ | i)
  · rfl
  · simp only [badPolarSystem, map_mul, map_linearPolynomial, RingHom.map_det,
      RingHom.mapMatrix_apply, map_squarePolynomial]
  · exact map_polarPolynomial φ w f i

end Map
end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.RankTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma exists_matrix_right_inverse {K α β : Type*} [Field K] [Fintype α] [Fintype β] [DecidableEq α]
    (A : Matrix α β K) (hA : Function.Surjective A.mulVec) :
    ∃ B : Matrix β α K, A * B = 1 := by
  classical
  choose b hb using fun i : α => hA (Pi.single i 1)
  refine ⟨fun j i => b i j, ?_⟩
  ext i j
  change (A.mulVec (b j)) i = (1 : Matrix α α K) i j
  rw [hb]
  simp [Matrix.one_apply, Pi.single_apply]

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

theorem polynomial_rank_specialize {K L σ α β : Type*}
    [Field K] [Field L] [Algebra K L] [Infinite K] [Fintype α] [Fintype β]
    (P : Matrix α β (MvPolynomial σ K)) (x : σ → L)
    (hP : Function.Surjective (P.map (eval₂Hom (algebraMap K L) x)).mulVec) :
    ∃ y : σ → K,
      Function.Surjective (P.map (eval₂Hom (RingHom.id K) y)).mulVec := by
  classical
  let τ := σ ⊕ (β × α)
  let A : Matrix α β (MvPolynomial τ K) := P.map (rename Sum.inl)
  let B : Matrix β α (MvPolynomial τ K) := fun i j => X (Sum.inr (i,j))
  let p : MvPolynomial τ K := (A*B).det
  obtain ⟨b,hb⟩ := exists_matrix_right_inverse _ hP
  let z : τ → L := Sum.elim x (fun ij => b ij.1 ij.2)
  let φ : MvPolynomial τ K →+* L := eval₂Hom (algebraMap K L) z
  have hA : A.map φ = P.map (eval₂Hom (algebraMap K L) x) := by
    ext i j
    simp [A, φ, z, Matrix.map_apply, eval₂_rename, Function.comp_def]
  have hB : B.map φ = b := by
    ext i j
    change φ (X (Sum.inr (i,j))) = b i j
    exact eval₂_X _ _ _
  have hp : φ p = 1 := by
    rw [show φ p = (φ.mapMatrix (A*B)).det from RingHom.map_det φ (A*B)]
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hA, hB, hb]
    exact Matrix.det_one
  have hpn : p ≠ 0 := by
    intro h
    have : (0 : L) = 1 := by simpa only [h, map_zero] using hp
    exact zero_ne_one this
  obtain ⟨w,hw⟩ : ∃ w : τ → K, eval w p ≠ 0 := by
    by_contra h
    apply hpn
    apply MvPolynomial.funext
    intro w
    simp only [map_zero]
    exact not_not.mp (not_exists.mp h w)
  let ψ : MvPolynomial τ K →+* K := eval₂Hom (RingHom.id K) w
  have hψ : ψ p ≠ 0 := by
    exact hw
  have hu : IsUnit ((A*B).map ψ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr hψ
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  refine ⟨fun i => w (Sum.inl i), ?_⟩
  have hAL : A.map ψ = P.map (eval₂Hom (RingHom.id K) (fun i => w (Sum.inl i))) := by
    ext i j
    simp [A, ψ, Matrix.map_apply, eval₂_rename, Function.comp_def]
  intro v
  obtain ⟨t,ht⟩ := hs v
  refine ⟨(B.map ψ).mulVec t, ?_⟩
  rw [← hAL, Matrix.mulVec_mulVec]
  simpa only [Matrix.map_mul] using ht

end PermanentBorder.SliceParameters

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

lemma smooth_extension {K L σ : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    [Fintype σ] (f : MvPolynomial σ K)
    (hs : ∀ y : σ → K, eval y f = 0 → (∀ j, eval y (pderiv j f) = 0) → y = 0)
    (y : σ → L) (hf : aeval y f = 0) (hd : ∀ j, aeval y (pderiv j f) = 0) : y = 0 := by
  classical
  let F : Option σ → MvPolynomial σ K := fun i => match i with
    | none => f
    | some j => pderiv j f
  let I := Ideal.span (Set.range F)
  have hz : ∀ x ∈ zeroLocus K I, x = 0 := by
    intro x hx
    apply hs x
    · exact hx _ (Ideal.subset_span ⟨none,rfl⟩)
    · intro j
      exact hx _ (Ideal.subset_span ⟨some j,rfl⟩)
  have hy : y ∈ zeroLocus L I := by
    rw [zeroLocus_span]
    rintro _ ⟨i,rfl⟩
    cases i with
    | none => exact hf
    | some j => exact hd j
  ext j
  obtain ⟨n,hn⟩ := variable_power_certificate I hz j
  have hpow : y j ^ n = 0 := by simpa using hy _ hn
  by_contra h
  exact pow_ne_zero n h hpow

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

lemma generic_bad_zero (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → K, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0)
    (y : PolarVars τ → E)
    (hy : ∀ i, eval y (badPolarSystem genericDirections genericLinear (map (algebraMap K E) f) i) = 0) :
    y = 0 := by
  classical
  by_contra hyn
  have hf : aeval y f = 0 := by simpa [badPolarSystem, eval_map, aeval_def] using hy none
  have hp : ∀ i, polarValue genericDirections f y i = 0 := by
    intro i
    simpa only [badPolarSystem, eval_polarPolynomial] using hy (some (some i))
  have hg : ∃ j, aeval y (pderiv j f) ≠ 0 := by
    by_contra h
    exact hyn (smooth_extension f hs y hf (by simpa only [not_exists, not_not] using h))
  have hn : ∑ j, genericLinear j * y j ≠ 0 := fun h =>
    hyn (generic_no_infinity f hh y hf hp hg h)
  have hu := generic_square_isUnit f hh y hf hp hyn hg
  have hj : (squareJacobian genericDirections genericLinear f y).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hb := hy (some none)
  simp only [badPolarSystem, map_mul, eval_linearPolynomial, RingHom.map_det,
    RingHom.mapMatrix_apply, eval_squarePolynomial] at hb
  exact (mul_ne_zero hn hj) hb

omit [CharZero K] [IsAlgClosed K] in
lemma universalBadPolar_specialize {L : Type*} [Field L] [Algebra K L]
    (f : MvPolynomial (PolarVars τ) K) (w : P → L) (i : PolarVars τ) :
    map (eval₂Hom (algebraMap K L) w) (universalBadPolar f i) =
      badPolarSystem (fun i j => w (some i,j)) (fun j => w (none,j))
        (map (algebraMap K L) f) i := by
  rw [universalBadPolar, map_badPolarSystem, MvPolynomial.map_map]
  have hc : (eval₂Hom (algebraMap K L) w).comp C = algebraMap K L := by ext; simp
  rw [hc]
  simp only [MvPolynomial.eval₂Hom_X']

theorem exists_good_polar_certificate (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → K, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → K, ∃ l : PolarVars τ → K, ∃ D : ℕ,
      Function.Surjective (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
        (badPolarSystem w l f) D).mulVec := by
  classical
  let F := badPolarSystem (genericDirections (K := K) (τ := τ)) genericLinear
    (map (algebraMap K E) f)
  have hhom (i : PolarVars τ) : (F i).IsHomogeneous (badPolarDegrees τ r i) :=
    badPolarSystem_homogeneous _ _ (hh.map _) i
  have hz : ∀ y ∈ zeroLocus E (Ideal.span (Set.range F)), y = 0 := by
    intro y hy
    apply generic_bad_zero f hh hs y
    intro i
    exact hy _ Ideal.mem_span_range_self
  obtain ⟨D,hD⟩ := homogeneous_piece_certificate (Ideal.span (Set.range F)) hz
  have hM : Function.Surjective
      (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) F D).mulVec := by
    apply (macaulay_surjective_iff _ _ (fun i => homogeneous_intWeight (hhom i)) D).mpr
    intro p hp
    exact hD p (intWeight_homogeneous hp)
  let M := macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) (universalBadPolar f) D
  have hMa : Function.Surjective (M.map (eval₂Hom (algebraMap K E) (genericParameter K P))).mulVec := by
    have he : M.map (eval₂Hom (algebraMap K E) (genericParameter K P)) =
        macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) F D := by
      rw [← macaulayMatrix_map]
      apply congrArg (fun Q => macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) Q D)
      funext i
      exact universalBadPolar_specialize f (genericParameter K P) i
    rwa [he]
  obtain ⟨a,ha⟩ := polynomial_rank_specialize M (genericParameter K P) hMa
  refine ⟨fun i j => a (some i,j), fun j => a (none,j), D, ?_⟩
  have he : M.map (eval₂Hom (RingHom.id K) a) =
      macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
        (badPolarSystem (fun i j => a (some i,j)) (fun j => a (none,j)) f) D := by
    rw [← macaulayMatrix_map]
    apply congrArg (fun Q => macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) Q D)
    funext i
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using universalBadPolar_specialize f a i
  rwa [he] at ha

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

lemma hypersurfacePolars_homogeneous (w : τ → PolarVars τ → ℂ)
    {f : MvPolynomial (PolarVars τ) ℂ} {r : ℕ} (hh : f.IsHomogeneous r) (i : Option τ) :
    (hypersurfacePolars w f i).IsHomogeneous (hypersurfaceDegrees r i) := by
  cases i with
  | none => exact hh
  | some i => exact polarPolynomial_homogeneous w hh i

lemma hypersurfacePolars_square (w : τ → PolarVars τ → ℂ) (l : PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) :
    CI.square (hypersurfacePolars w f) l =
      (squarePolynomial w l f).submatrix swapFirstRows id := by
  ext i j
  rcases i with _ | (_ | i) <;>
    simp [CI.square, hypersurfacePolars, squarePolynomial, Matrix.submatrix, swapFirstRows]

lemma determinant_permutation_ne_zero {n : Type*} [Fintype n]
    (d₁ d₂ : DecidableEq n) (A B : Matrix n n ℂ) (e : Equiv.Perm n)
    (he : B = A.submatrix e id) (ha : @Matrix.det n d₁ _ ℂ _ A ≠ 0) :
    @Matrix.det n d₂ _ ℂ _ B ≠ 0 := by
  subst B
  cases Subsingleton.elim d₁ d₂
  rw [Matrix.det_permute]
  exact mul_ne_zero (by exact_mod_cast (Equiv.Perm.sign e).ne_zero) ha

lemma polar_certificate_good (w : τ → PolarVars τ → ℂ) (l : PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) {r : ℕ} (hh : f.IsHomogeneous r) (D : ℕ)
    (hM : Function.Surjective (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
      (badPolarSystem w l f) D).mulVec) : CI.Good (hypersurfacePolars w f) l := by
  classical
  have hz := macaulay_surjective_zero (badPolarSystem w l f) (badPolarDegrees τ r)
    (badPolarSystem_homogeneous w l hh) D hM
  intro y hn hy
  have hp : eval y (linearPolynomial l) * ((squarePolynomial w l f).map (eval y)).det ≠ 0 := by
    intro he
    apply hn (hz y ?_)
    rintro (_ | (_ | i))
    · exact hy none
    · simpa only [badPolarSystem, map_mul, RingHom.map_det, RingHom.mapMatrix_apply] using he
    · exact hy (some i)
  refine ⟨(mul_ne_zero_iff.mp hp).1, ?_⟩
  have he : (CI.square (hypersurfacePolars w f) l).map (eval y) =
      ((squarePolynomial w l f).map (eval y)).submatrix swapFirstRows id := by
    rw [hypersurfacePolars_square]
    rfl
  exact determinant_permutation_ne_zero _ _ _ _ swapFirstRows he (mul_ne_zero_iff.mp hp).2

theorem smooth_polar_count (f : MvPolynomial (PolarVars τ) ℂ) {r : ℕ} (hr : 2 ≤ r)
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ, ∃ l : PolarVars τ → ℂ,
      CI.Good (hypersurfacePolars w f) l ∧
      Nat.card (CI.Roots (hypersurfacePolars w f) l) = r * (r-1) ^ Fintype.card τ := by
  obtain ⟨w,l,D,hD⟩ := exists_good_polar_certificate f hh hs
  have hg := polar_certificate_good w l f hh D hD
  refine ⟨w,l,hg,?_⟩
  have hc := CI.good_card (hypersurfacePolars w f) l (hypersurfaceDegrees r)
    (by rintro (_ | i) <;> simp only [hypersurfaceDegrees,Option.elim'_none,Option.elim'_some] <;> omega)
    (hypersurfacePolars_homogeneous w hh) hg
  simpa [hypersurfaceDegrees] using hc

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma coordinateSplit_none (l : Option ι → ℂ) (h : l none ≠ 0) (y : Option ι → ℂ) :
    coordinateSplit l h y none = ∑ j, l j * y j := rfl

lemma exists_normalizer_equiv (l : Option ι → ℂ) (hl : l ≠ 0) :
    ∃ e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ),
      ∀ y, e y none = ∑ j, l j * y j := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra! h
    exact hl (funext h)
  let p := Equiv.swap none i
  let c : (Option ι → ℂ) ≃ₗ[ℂ] (Option ι → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ p.symm
  have hc (y : Option ι → ℂ) (j : Option ι) : c y j = y (p j) := rfl
  let l' := fun j => l (p j)
  have hl' : l' none ≠ 0 := by simpa [l',p] using hi
  let e := c.trans (coordinateSplit l' hl')
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  intro y
  change (coordinateSplit l' hl' (c y)) none = _
  rw [coordinateSplit_none]
  change (∑ j, l (p j) * y (p j)) = _
  exact Equiv.sum_comp p (fun j => l j * y j)

lemma affineNormChart_hasFDerivAt
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) :
    HasFDerivAt (affineNormChart e)
      (e.symm.toContinuousLinearMap.comp optionInsert) z := by
  have h : HasFDerivAt (fun z : ι → ℂ => Option.elim' 1 z) optionInsert z := by
    apply hasFDerivAt_pi.mpr
    rintro (_ | i)
    · exact hasFDerivAt_const _ _
    · exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt
  exact e.symm.hasFDerivAt.comp z h

omit [Fintype ι] in
lemma exists_chart_preimage
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) {y : Option ι → ℂ}
    (hy : e y none = 1) : ∃ z, affineNormChart e z = y := by
  refine ⟨fun i => e y (some i), ?_⟩
  apply e.injective
  rw [affineNormChart, e.apply_symm_apply]
  funext i
  cases i <;> simp [hy]

lemma affineNormChart_eq
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) (j : Option ι) :
    affineNormChart e z j = e.symm (Pi.single none 1) j +
      ∑ i, e.symm (Pi.single (some i) 1) j * z i := by
  classical
  have hd : Option.elim' 1 z = Pi.single none 1 + ∑ i, z i • Pi.single (some i) 1 := by
    funext j
    cases j <;> simp [Pi.single_apply]
  rw [affineNormChart, hd, map_add, map_sum]
  simp [Finset.sum_apply, mul_comm]

end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma isInvertible_of_injective (D : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hD : Function.Injective D) : D.IsInvertible := by
  have hs : Function.Surjective D := (LinearMap.injective_iff_surjective).mp hD
  let e := LinearEquiv.ofBijective D.toLinearMap ⟨hD,hs⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

lemma normalizer_simple_restrict
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ))
    (F : (Option ι → ℂ) → (Option ι → ℂ))
    (hfirst : ∀ y, F y none = e y none - 1) (z : ι → ℂ)
    (hF : DifferentiableAt ℂ F (affineNormChart e z))
    (hs : (fderiv ℂ F (affineNormChart e z)).IsInvertible) :
    (fderiv ℂ (fun z i => F (affineNormChart e z) (some i)) z).IsInvertible := by
  let D := (fderiv ℂ F (affineNormChart e z)).comp
    (e.symm.toContinuousLinearMap.comp optionInsert)
  have hfull : HasFDerivAt (fun z => F (affineNormChart e z)) D z :=
    hF.hasFDerivAt.comp z (affineNormChart_hasFDerivAt e z)
  let E : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi (fun i => (ContinuousLinearMap.proj (some i)).comp D)
  have hred : HasFDerivAt (fun z i => F (affineNormChart e z) (some i)) E z :=
    hasFDerivAt_pi.mpr (fun i => (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hfull)
  have hzero : (fun z => F (affineNormChart e z) none) = fun _ => (0 : ℂ) := by
    funext z
    rw [hfirst, affineNormChart, e.apply_symm_apply]
    simp
  have hnone : (ContinuousLinearMap.proj none).comp D = 0 := by
    have hd := (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hfull
    change HasFDerivAt (fun z => F (affineNormChart e z) none) _ z at hd
    rw [hzero] at hd
    exact hd.unique (hasFDerivAt_const _ _)
  rw [hred.fderiv]
  apply isInvertible_of_injective
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hd : D v = 0 := by
    funext i
    cases i with
    | none => exact congrArg (fun T : (ι → ℂ) →L[ℂ] ℂ => T v) hnone
    | some i => exact congrFun hv i
  have he : e.symm (optionInsert v) = 0 := hs.injective (hd.trans (map_zero _).symm)
  have hi : optionInsert v = 0 := e.symm.injective (he.trans (map_zero _).symm)
  exact funext (fun i => congrFun hi (some i))

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

theorem smooth_polar_affine_certificate (f : MvPolynomial (PolarVars τ) ℂ)
    {r : ℕ} (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ,
    ∃ e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ),
    ∃ x : Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ,
      Function.Injective x ∧
      ∀ i, (fun j => eval (affineNormChart e (x i)) (hypersurfacePolars w f j)) = 0 ∧
        (fderiv ℂ (fun z j => eval (affineNormChart e z)
          (hypersurfacePolars w f j)) (x i)).IsInvertible := by
  classical
  obtain ⟨w,l,hg,hcard⟩ := smooth_polar_count f hr hh hs
  let R := CI.Roots (hypersurfacePolars w f) l
  have hpos : 0 < Nat.card R := by
    rw [show Nat.card R = _ from hcard]
    exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have : Finite R := (Nat.card_pos_iff.mp hpos).2
  let : Fintype R := Fintype.ofFinite R
  have hcard' : Fintype.card R = r * (r-1)^Fintype.card τ := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let q : Fin (r * (r-1)^Fintype.card τ) ≃ R := (Fintype.equivFinOfCardEq hcard').symm
  have hl : l ≠ 0 := by
    intro hz
    obtain ⟨y⟩ := (Nat.card_pos_iff.mp hpos).1
    have hy := y.property.2
    simp [CI.eval_linear, hz] at hy
  obtain ⟨e,he⟩ := exists_normalizer_equiv l hl
  have hy (i : Fin (r * (r-1)^Fintype.card τ)) : e (q i).val none = 1 := by
    rw [he, ← CI.eval_linear]
    exact (q i).property.2
  choose x hx using fun i => exists_chart_preimage e (hy i)
  refine ⟨w,e,x,?_,?_⟩
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    rw [← hx i, ← hx j, hij]
  · intro i
    have hz : (fun j => eval (q i).val (CI.normalized (hypersurfacePolars w f) l j)) = 0 :=
      (CI.normalized_eval_zero_iff _ _ _).mpr (q i).property
    constructor
    · rw [hx i]
      exact funext (q i).property.1
    · have hfirst (y : PolarVars τ → ℂ) :
          eval y (CI.normalized (hypersurfacePolars w f) l none) = e y none - 1 := by
        change eval y (CI.linear l - 1) = _
        rw [map_sub, map_one, CI.eval_linear, he]
      apply normalizer_simple_restrict e
        (fun y j => eval y (CI.normalized (hypersurfacePolars w f) l j)) hfirst (x i)
      · exact ((contDiff_pi.mpr (fun j => CI.contDiff_eval
          (CI.normalized (hypersurfacePolars w f) l j))).differentiable (by decide)) _
      · rw [hx i]
        exact CI.good_derivative_invertible _ _ _ hg hz

end PermanentBorder.Polar

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

theorem support_subset_exponentCube {P : Poly σ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    P.support ⊆ exponentCube n := by
  intro d hd
  rw [mem_exponentCube]
  intro i
  exact (monomial_le_degreeOf i hd).trans ((degreeOf_le_totalDegree P i).trans hP)

theorem sum_over_exponentCube {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) :
    P = ∑ d ∈ exponentCube n, monomial d (P.coeff d) := by
  calc
    P = ∑ d ∈ P.support, monomial d (P.coeff d) := MvPolynomial.as_sum P
    _ = _ := ?_
  apply Finset.sum_subset hP
  intro d _ hd
  simp only [notMem_support_iff.mp hd, map_zero]

theorem coeff_linear_map_cube (F : Poly σ →ₗ[ℂ] Poly τ) {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) (e : τ →₀ ℕ) :
    (F P).coeff e = ∑ d ∈ exponentCube n,
      P.coeff d * (F (monomial d 1)).coeff e := by
  conv_lhs => rw [sum_over_exponentCube hP]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by simp [smul_monomial],
    map_smul, coeff_smul, smul_eq_mul]

theorem support_subset_cube_of_limit {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    p.support ⊆ exponentCube n := by
  classical
  intro d hd
  by_contra hn
  have hz : ∀ j, (P j).coeff d = 0 := by
    intro j
    apply notMem_support_iff.mp
    exact fun hj => hn (hP j hj)
  have ht : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (p.coeff d)) := by
    simpa only [hz] using hp d
  have he : p.coeff d = 0 := (tendsto_nhds_unique tendsto_const_nhds ht).symm
  exact mem_support_iff.mp hd he

theorem coefficientwise_linear_map_limit (F : Poly σ →ₗ[ℂ] Poly τ)
    {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    ∀ e, Tendsto (fun j => (F (P j)).coeff e) atTop (𝓝 ((F p).coeff e)) := by
  intro e
  have hc := support_subset_cube_of_limit hP hp
  have ht := tendsto_finsetSum (exponentCube (σ := σ) n)
    (fun d _ => (hp d).mul (tendsto_const_nhds (x := (F (monomial d 1)).coeff e)))
  convert ht using 1
  · funext j
    exact coeff_linear_map_cube F (hP j) e
  · congr 1
    exact coeff_linear_map_cube F hc e
end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

theorem degree_affine_form (b : ℂ) (a : σ → ℂ) :
    (C b + ∑ v : σ, C (a v) * X v : Poly σ).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro v _
    exact (totalDegree_mul _ _).trans (by simp)

theorem degree_affineMatrixPolynomial (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    (affineMatrixPolynomial n A₀ A).totalDegree ≤ n := by
  classical
  unfold affineMatrixPolynomial
  have he := Matrix.det_apply (show Matrix (Fin n) (Fin n) (Poly σ) from
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  rw [he]
  apply totalDegree_finsetSum_le
  intro s _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun i _ => degree_affine_form _ _
    _ = n := by simp
end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem affineSubstitution_matrix (b : σ → ℂ) (B : σ → τ → ℂ)
    (n : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineSubstitution b B (affineMatrixPolynomial n A₀ A) =
      affineMatrixPolynomial n
        (fun i j => A₀ i j + ∑ v : σ, A v i j * b v)
        (fun w i j => ∑ v : σ, A v i j * B v w) := by
  classical
  unfold affineMatrixPolynomial
  have he := RingHom.map_det (affineSubstitution b B).toRingHom
    (show Matrix (Fin n) (Fin n) (Poly σ) from
      fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  refine he.trans ?_
  apply congrArg Matrix.det
  funext i j
  change (affineSubstitution b B) (C (A₀ i j) + ∑ v, C (A v i j) * X v) =
    C (A₀ i j + ∑ v, A v i j * b v) + ∑ w, C (∑ v, A v i j * B v w) * X w
  simp only [affineSubstitution, map_add, map_sum, map_mul,
    aeval_C, aeval_X, algebraMap_eq]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← map_mul]
  rw [← add_assoc]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, map_mul, mul_assoc]

theorem HasBorderDeterminant.affineSubstitution {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (b : σ → ℂ) (B : σ → τ → ℂ) :
    HasBorderDeterminant n (affineSubstitution b B p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  refine ⟨hn,
    (fun l i j => A₀ l i j + ∑ v : σ, A l v i j * b v),
    (fun l w i j => ∑ v : σ, A l v i j * B v w), ?_⟩
  have hf := coefficientwise_linear_map_limit (PermanentBorder.affineSubstitution b B).toLinearMap
    (fun l => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ l) (A l))) hlim
  intro e
  simpa only [AlgHom.toLinearMap_apply, affineSubstitution_matrix] using hf e
end AffineSubstitution
end PermanentBorder

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.BorderPolars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis
open MvPolynomial Filter
open scoped Topology

section PolynomialSystem
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem contDiff_coefficientSystem (n : ℕ) (L : τ → Poly σ →ₗ[ℂ] Poly τ) :
    ContDiff ℂ 1 (coefficientSystem n L) := by
  classical
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro d _
  exact ((contDiff_apply ℂ ℂ d).comp contDiff_fst).mul
    ((contDiff_mvPolynomial_eval _).comp contDiff_snd)

omit [Fintype τ] in
theorem coefficientSystem_eq {n : ℕ} (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    {P : Poly σ} (hP : P.support ⊆ exponentCube n) (x : τ → ℂ) :
    coefficientSystem n L ((fun d => P.coeff d.val),x) = polynomialSystem L P x := by
  classical
  ext i
  change (∑ d : exponentCube n, P.coeff d.val * eval x (L i (monomial d.val 1))) = _
  change _ = eval x (L i P)
  conv_rhs => rw [sum_over_exponentCube hP]
  simp only [map_sum]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d.val (P.coeff d.val) = P.coeff d.val • monomial d.val (1 : ℂ) by
    simp [smul_monomial], map_smul]
  simp

theorem coefficient_limit_simple_zeros {ι : Type*} [Fintype ι]
    (L : τ → Poly σ →ₗ[ℂ] Poly τ) {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d)))
    (x : ι → τ → ℂ) (hx : Function.Injective x)
    (hs : ∀ i, SimplePolynomialZero L p (x i)) :
    ∀ᶠ j in atTop, ∃ y : ι → τ → ℂ, Function.Injective y ∧
      ∀ i, SimplePolynomialZero L (P j) (y i) := by
  classical
  let c : exponentCube (σ := σ) n → ℂ := fun d => p.coeff d.val
  let cs : ℕ → exponentCube (σ := σ) n → ℂ := fun j d => (P j).coeff d.val
  have hc : Tendsto cs atTop (𝓝 c) := tendsto_pi_nhds.mpr fun d => hp d.val
  let F := coefficientSystem n L
  have hF : ContDiff ℂ 1 F := contDiff_coefficientSystem n L
  have hp' := support_subset_cube_of_limit hP hp
  have he : (fun x => F (c,x)) = polynomialSystem L p := by
    funext x
    exact coefficientSystem_eq L hp' x
  have hz : ∀ i, F (c,x i) = 0 := by
    intro i
    rw [congrFun he]
    exact (hs i).1
  have hs' : ∀ i, SimpleAt F c (x i) := by
    intro i
    unfold SimpleAt
    rw [← fderiv_slice hF, he]
    exact (hs i).2
  have ht := finite_simple_zeros_persist hF x hx hz hs'
  filter_upwards [hc.eventually ht] with j hj
  obtain ⟨y,hy,hys⟩ := hj
  refine ⟨y,hy,?_⟩
  intro i
  have he' : (fun x => F (cs j,x)) = polynomialSystem L (P j) := by
    funext x
    exact coefficientSystem_eq L (hP j) x
  constructor
  · rw [← congrFun he']
    exact (hys i).1
  · rw [← he', fderiv_slice hF]
    exact (hys i).2

theorem HasBorderDeterminant.exists_simple_approximant {ι : Type*} [Fintype ι]
    {p : Poly σ} {n : ℕ} (h : HasBorderDeterminant n p)
    (L : τ → Poly σ →ₗ[ℂ] Poly τ) (x : ι → τ → ℂ)
    (hx : Function.Injective x) (hs : ∀ i, SimplePolynomialZero L p (x i)) :
    ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ)
      (y : ι → τ → ℂ), Function.Injective y ∧
      ∀ i, SimplePolynomialZero L (affineMatrixPolynomial n A₀ A) (y i) := by
  obtain ⟨hn,A₀,A,hlim⟩ := h
  obtain ⟨j,y,hy,hys⟩ := (coefficient_limit_simple_zeros L
    (fun j => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ j) (A j)))
    hlim x hx hs).exists
  exact ⟨A₀ j,A j,y,hy,hys⟩
end PolynomialSystem
end PermanentBorder.PolarAnalysis
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

lemma eval_affineChartSubstitution
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ))
    (f : Poly (PolarVars τ)) (z : Option τ → ℂ) :
    eval z (affineChartSubstitution e f) = eval (affineNormChart e z) f := by
  change (aeval z : Poly (Option τ) →ₐ[ℂ] ℂ) (aeval _ f) = _
  rw [comp_aeval_apply]
  apply congrArg (fun g : PolarVars τ → ℂ => aeval g f)
  funext j
  simp only [map_add, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
  convert (affineNormChart_eq e z j).symm using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply congrArg (fun v : PolarVars τ → ℂ => e.symm v j)
  funext v
  simp [Pi.single_apply]

lemma polarOperator_eq (w : τ → PolarVars τ → ℂ) (i : τ) (f : Poly (PolarVars τ)) :
    polarOperator w i f = polarPolynomial w f i := by
  simp [polarOperator, polarPolynomial, smul_eq_C_mul]

lemma polynomialSystem_affinePolarOperators (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) (f : Poly (PolarVars τ)) :
    PolarAnalysis.polynomialSystem (affinePolarOperators w e) f =
      fun z j => eval (affineNormChart e z) (hypersurfacePolars w f j) := by
  funext z j
  cases j with
  | none => exact eval_affineChartSubstitution e f z
  | some i =>
    change eval z (affineChartSubstitution e (polarOperator w i f)) = _
    rw [eval_affineChartSubstitution, polarOperator_eq]
    rfl

theorem HasBorderDeterminant.simple_polar_approximant {n r : ℕ}
    {f : Poly (PolarVars τ)} (hb : HasBorderDeterminant n f)
    (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ,
    ∃ e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ),
    ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : PolarVars τ → Matrix (Fin n) (Fin n) ℂ),
    ∃ x : Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ,
      Function.Injective x ∧ ∀ i,
        PolarAnalysis.SimplePolynomialZero (affinePolarOperators w e)
          (affineMatrixPolynomial n A₀ A) (x i) := by
  obtain ⟨w,e,x,hx,hsx⟩ := smooth_polar_affine_certificate f hr hh hs
  have hp (i) : PolarAnalysis.SimplePolynomialZero (affinePolarOperators w e) f (x i) := by
    unfold PolarAnalysis.SimplePolynomialZero
    rw [polynomialSystem_affinePolarOperators]
    exact hsx i
  obtain ⟨A₀,A,y,hy,hys⟩ := PolarAnalysis.HasBorderDeterminant.exists_simple_approximant
    hb (affinePolarOperators w e) x hx hp
  exact ⟨w,e,A₀,A,y,hy,hys⟩
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PolarAnalysis KernelBilinear
open scoped Classical
variable {τ : Type} [Fintype τ]

lemma derivative_polar (w : τ → PolarVars τ → ℂ) (f : Poly (PolarVars τ))
    (y : PolarVars τ → ℂ) (i : τ) :
    fderiv ℂ (fun y => eval y f) y (w i) = eval y (polarPolynomial w f i) := by
  rw [(CI.hasFDerivAt_eval f y).fderiv, CI.polynomialDerivative_apply]
  simp [polarPolynomial,mul_comm]

lemma polarPair_polynomialSystem (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) (f : Poly (PolarVars τ)) :
    polarPair (fun y => eval y f) (fun z => affineNormChart e (optionProduct.symm z)) w =
      fun z => optionProduct (polynomialSystem (affinePolarOperators w e) f (optionProduct.symm z)) := by
  funext z
  rw [polynomialSystem_affinePolarOperators]
  apply Prod.ext
  · rfl
  · funext i
    exact derivative_polar w f _ i

omit [Fintype τ] in
lemma affineNormChart_add (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ))
    (z : Option τ → ℂ) :
    affineNormChart e z = e.symm (Pi.single none 1) +
      (e.symm.toContinuousLinearMap.comp optionInsert) z := by
  change e.symm (Option.elim' 1 z) = e.symm (Pi.single none 1) + e.symm (optionInsert z)
  rw [← map_add]
  apply congrArg e.symm
  funext j
  cases j <;> simp

lemma eval_matrix {σ : Type} [Fintype σ] {n : ℕ}
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :
    eval y (affineMatrixPolynomial (n+1) A₀ A) = (affine A₀ A y).det := by
  classical
  let M : Matrix (Fin (n+1)) (Fin (n+1)) (Poly σ) :=
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v
  change eval y M.det = _
  calc
    eval y M.det = ((eval y).mapMatrix M).det := RingHom.map_det (eval y) M
    _ = (affine A₀ A y).det := by
      apply congrArg Matrix.det
      ext i j
      change eval y (M i j) = (affine A₀ A y) i j
      simp [M,affine,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_comm]

lemma simple_conjugate {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (e : V ≃L[ℂ] W) {F : V → V} {x : V} (hF : DifferentiableAt ℂ F x)
    (hs : (fderiv ℂ F x).IsInvertible) :
    (fderiv ℂ (fun y => e (F (e.symm y))) (e x)).IsInvertible := by
  have hF' : HasFDerivAt F (fderiv ℂ F x) (e.symm (e x)) := by simpa using hF.hasFDerivAt
  have hd := e.hasFDerivAt.comp (e x)
    (hF'.comp (e x) e.symm.hasFDerivAt)
  change (fderiv ℂ (e ∘ F ∘ e.symm) (e x)).IsInvertible
  rw [hd.fderiv]
  exact (show e.toContinuousLinearMap.IsInvertible from ⟨e,rfl⟩).comp
    (hs.comp (show e.symm.toContinuousLinearMap.IsInvertible from ⟨e.symm,rfl⟩))

theorem HasBorderDeterminant.polar_count {n r : ℕ}
    {f : Poly (PolarVars τ)} (hb : HasBorderDeterminant n f)
    (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    r * (r-1)^Fintype.card τ ≤
      2^Fintype.card τ * (2*n-1).choose (Fintype.card τ+1) := by
  classical
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hb.1)
  | succ n =>
    obtain ⟨w,e,A₀,A,x,hx,hxs⟩ := HasBorderDeterminant.simple_polar_approximant hb hr hh hs
    let P := affineMatrixPolynomial (n+1) A₀ A
    let Q := polynomialSystem (affinePolarOperators w e) P
    let b := e.symm (Pi.single none 1)
    let L := e.symm.toContinuousLinearMap.comp optionInsert
    have hrel : polarPair (fun y => (affine A₀ A y).det)
        (fun z => b + L (optionProduct.symm z)) w =
          fun z => optionProduct (Q (optionProduct.symm z)) := by
      have heval : (fun y => (affine A₀ A y).det) = (fun y => eval y P) := by
        funext y
        exact (eval_matrix A₀ A y).symm
      have hψ : (fun z => b + L (optionProduct.symm z)) =
          (fun z => affineNormChart e (optionProduct.symm z)) := by
        funext z
        exact (affineNormChart_add e _).symm
      rw [heval,hψ]
      exact polarPair_polynomialSystem w e P
    have hQ (z : Option τ → ℂ) : DifferentiableAt ℂ Q z := by
      apply differentiableAt_pi.mpr
      intro j
      exact ((contDiff_mvPolynomial_eval ((affinePolarOperators w e j) P)).differentiable (by decide)).differentiableAt
    have hcount := affine_polar_count A₀ A b L w (fun j => optionProduct (x j))
      (optionProduct.injective.comp hx)
      (fun j => by
        rw [hrel]
        change optionProduct (Q (optionProduct.symm (optionProduct (x j)))) = 0
        rw [optionProduct.symm_apply_apply]
        have hz : Q (x j) = 0 := (hxs j).1
        rw [hz, map_zero])
      (fun j => by
        rw [hrel]
        exact simple_conjugate optionProduct (hQ (x j)) (hxs j).2)
    have hn : 2*(n+1)-1 = 2*n+1 := by omega
    simpa [hn] using hcount
end PermanentBorder.Polar

namespace PermanentBorder.Polar

 theorem factorial_exp_lower (b : ℕ) : ((b : ℝ) / Real.exp 1)^b ≤ b.factorial := by
  rcases b with _ | b
  · simp
  have hb : (1:ℝ) ≤ b+1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
  have hπ : (1:ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (b+1)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  have hn := Stirling.le_factorial_stirling (b+1)
  simp only [Nat.cast_add, Nat.cast_one] at hn ⊢
  exact le_trans (le_mul_of_one_le_left (by positivity) hs) hn

 theorem choose_exp_bound (a b : ℕ) (hb : 0 < b) :
    (a.choose b : ℝ) ≤ (Real.exp 1 * a / b)^b := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hfact := factorial_exp_lower b
  have hx : (0:ℝ) < ((b:ℝ)/Real.exp 1)^b := by positivity
  calc
    (a.choose b : ℝ) ≤ (a:ℝ)^b / b.factorial := Nat.choose_le_pow_div b a
    _ ≤ (a:ℝ)^b / ((b:ℝ)/Real.exp 1)^b :=
      div_le_div_of_nonneg_left (by positivity) hx hfact
    _ = (Real.exp 1 * a / b)^b := by rw [← div_pow]; congr 1; field_simp

 theorem smooth_count_numerical_bound (n K r : ℕ) (hn : 0 < n) (hr : 2 ≤ r)
    (hcount : (r:ℝ) * ((r-1:ℕ):ℝ)^K ≤
      2^K * ((2*n-1).choose (K+1) : ℝ)) :
    ((r-1:ℕ):ℝ) * (K+1) / (4 * Real.exp 1) ≤ n := by
  have hr0 : (0:ℝ) < (r-1:ℕ) := by exact_mod_cast (show 0 < r-1 by omega)
  have hrle : ((r-1:ℕ):ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hK : (0:ℝ) < K+1 := by positivity
  have hchoose := choose_exp_bound (2*n-1) (K+1) (by omega)
  have htwo : ((2*n-1:ℕ):ℝ) ≤ 2*n := by
    exact_mod_cast (Nat.sub_le (2*n) 1)
  have hbase : Real.exp 1 * ((2*n-1:ℕ):ℝ) / ((K+1:ℕ):ℝ) ≤
      (2 * Real.exp 1 * n) / (K+1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.exp_pos (1:ℝ)]
  have hpow : (((r-1:ℕ):ℝ))^(K+1) ≤ (4 * Real.exp 1 * n / (K+1))^(K+1) := by
    calc
      (((r-1:ℕ):ℝ))^(K+1) ≤ (r:ℝ) * ((r-1:ℕ):ℝ)^K := by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_right hrle (by positivity)
      _ ≤ 2^K * ((2*n-1).choose (K+1) : ℝ) := hcount
      _ ≤ 2^K * (Real.exp 1 * ((2*n-1:ℕ):ℝ) / ((K+1:ℕ):ℝ))^(K+1) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ ≤ 2^(K+1) * ((2 * Real.exp 1 * n) / (K+1))^(K+1) := by
        apply mul_le_mul
        · have : (2:ℝ)^K ≤ 2^(K+1) := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) K]
          exact this
        · exact pow_le_pow_left₀ (by positivity) hbase _
        · positivity
        · positivity
      _ = (4 * Real.exp 1 * n / (K+1))^(K+1) := by
        rw [← mul_pow]; congr 1; ring
  have hle : ((r-1:ℕ):ℝ) ≤ 4 * Real.exp 1 * n / (K+1) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : K+1 ≠ 0)).mp hpow
  apply (div_le_iff₀ (by positivity)).mpr
  have := (le_div_iff₀ hK).mp hle
  nlinarith

end PermanentBorder.Polar

namespace PermanentBorder
open MvPolynomial
open scoped Classical

theorem HasBorderDeterminant.rename {σ τ : Type*} [Fintype σ] [Fintype τ]
    {n : ℕ} {f : Poly σ} (h : HasBorderDeterminant n f) (e : σ → τ) :
    HasBorderDeterminant n (MvPolynomial.rename e f) := by
  classical
  let B : σ → τ → ℂ := fun i j => if e i = j then 1 else 0
  have he : PermanentBorder.affineSubstitution (fun _ : σ => 0) B = (MvPolynomial.rename e : Poly σ →ₐ[ℂ] Poly τ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [PermanentBorder.affineSubstitution,B,eq_comm]
  simpa only [he] using h.affineSubstitution (fun _ => 0) B

namespace Polar

lemma smooth_rename {σ τ : Type} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (f : Poly σ)
    (hs : ∀ y : σ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∀ y : τ → ℂ, eval y (rename e f) = 0 →
      (∀ j, eval y (pderiv j (rename e f)) = 0) → y = 0 := by
  intro y hy hg
  rw [eval_rename] at hy
  have hgrad (i : σ) : eval (y ∘ e) (pderiv i f) = 0 := by
    have h := hg (e i)
    rw [pderiv_rename e.injective,eval_rename] at h
    exact h
  have hz := hs _ hy hgrad
  funext i
  simpa only [Function.comp_apply,e.apply_symm_apply,Pi.zero_apply] using congrFun hz (e.symm i)

theorem HasBorderDeterminant.smooth_lower_bound_oai {σ : Type} [Fintype σ]
    {n r : ℕ} {f : Poly σ} (hb : HasBorderDeterminant n f)
    (hσ : 2 ≤ Fintype.card σ) (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : σ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ((r-1 : ℕ) : ℝ) * ((Fintype.card σ-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ n := by
  classical
  let K := Fintype.card σ - 2
  have hc : Fintype.card σ = Fintype.card (PolarVars (Fin K)) := by
    simp only [PolarVars,Fintype.card_option,Fintype.card_fin]
    dsimp [K]
    omega
  let e := Fintype.equivOfCardEq hc
  have hb' := hb.rename e
  have hp := HasBorderDeterminant.polar_count hb' hr (hh.rename_isHomogeneous)
    (smooth_rename e f hs)
  have hcount : (r : ℝ) * ((r-1 : ℕ) : ℝ)^K ≤
      2^K * ((2*n-1).choose (K+1) : ℝ) := by
    simp only [Fintype.card_fin] at hp
    exact_mod_cast hp
  have h := smooth_count_numerical_bound n K r hb.1 hr hcount
  have hk : K+1 = Fintype.card σ-1 := by dsimp [K]; omega
  have hkR : (K : ℝ)+1 = ((Fintype.card σ-1 : ℕ) : ℝ) := by exact_mod_cast hk
  simpa only [hkR] using h
end Polar
end PermanentBorder

end OAI
end

theorem solution : type_of% @OAI.PermanentBorder.Polar.HasBorderDeterminant.smooth_lower_bound_oai := @OAI.PermanentBorder.Polar.HasBorderDeterminant.smooth_lower_bound_oai
