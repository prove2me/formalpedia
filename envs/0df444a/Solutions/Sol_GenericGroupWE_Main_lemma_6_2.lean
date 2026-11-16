-- Prove2me | solution 1 for GenericGroupWE.Main.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T11:44:16.117161+00:00
-- url     : https://prove2.me/submissions/1340d66e-5249-4b14-9510-f2837a1d62bb

import Definitions.Def_GenericGroupWE_Main_Tables


namespace GenericGroupWE.Main
namespace SelectorProof

open scoped BigOperators

noncomputable def ofExponent {N e : ℕ} (d : Fin N →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≤ e) : OrdinaryMonomial N e := by
  classical
  refine ⟨fun i => ⟨d i, ?_⟩, ?_⟩
  · have hi : d i ≤ ∑ j : Fin N, d j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hs : (∑ j : Fin N, d j) ≤ e := by
      simpa [Finsupp.sum_fintype] using hd
    omega
  · simpa [Finsupp.sum_fintype] using hd

theorem polynomial_ofExponent {K : Type*} [Field K] {N e : ℕ}
    (d : Fin N →₀ ℕ) (hd : d.sum (fun _ n => n) ≤ e) :
    monomialPolynomial (K := K) (ofExponent d hd) = MvPolynomial.monomial d 1 := by
  classical
  have he : Finsupp.equivFunOnFinite.symm
      (fun j => ((ofExponent d hd).val j).val) = d := by
    ext j
    simp [ofExponent]
  unfold monomialPolynomial
  rw [he]

theorem monomial_degree_le {K : Type*} [Field K] {N e : ℕ}
    (u : OrdinaryMonomial N e) :
    (monomialPolynomial (K := K) u).totalDegree ≤ e := by
  unfold monomialPolynomial
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  simpa [Finsupp.sum_fintype] using u.property

/-- Split the list of factors after a factors; its two pieces fit the side bounds. -/
theorem split_monomial {K : Type*} [Field K] {N : ℕ} (a b : ℕ)
    (d : Fin N →₀ ℕ) (hd : d.sum (fun _ n => n) ≤ a+b) :
    ∃ (u : OrdinaryMonomial N a) (v : OrdinaryMonomial N b),
      MvPolynomial.monomial d (1 : K) = monomialPolynomial u * monomialPolynomial v := by
  classical
  let l := d.toMultiset.toList
  have hlen : l.length ≤ a+b := by
    simpa [l, Multiset.length_toList, Finsupp.card_toMultiset, Function.id_def] using hd
  let d1 := Multiset.toFinsupp ((l.take a : List (Fin N)) : Multiset (Fin N))
  let d2 := Multiset.toFinsupp ((l.drop a : List (Fin N)) : Multiset (Fin N))
  have hd1 : d1.sum (fun _ n => n) ≤ a := by
    change (Multiset.toFinsupp ((l.take a : List (Fin N)) : Multiset (Fin N))).sum
      (fun _ => id) ≤ a
    rw [Multiset.toFinsupp_sum_eq, Multiset.coe_card, List.length_take]
    exact Nat.min_le_left a l.length
  have hd2 : d2.sum (fun _ n => n) ≤ b := by
    change (Multiset.toFinsupp ((l.drop a : List (Fin N)) : Multiset (Fin N))).sum
      (fun _ => id) ≤ b
    rw [Multiset.toFinsupp_sum_eq, Multiset.coe_card, List.length_drop]
    omega
  have hadd : d1+d2 = d := by
    dsimp [d1, d2]
    rw [← Multiset.toFinsupp_add, Multiset.coe_add, List.take_append_drop]
    simp [l]
  refine ⟨ofExponent d1 hd1, ofExponent d2 hd2, ?_⟩
  rw [polynomial_ofExponent, polynomial_ofExponent, MvPolynomial.monomial_mul,
    one_mul, hadd]

theorem table_zero_iff {K : Type*} [Field K] {N : ℕ} (a b : ℕ)
    (L : MvPolynomial (Fin N) K →ₗ[K] K) :
    rectangularTable a b L = 0 ↔
      ∀ f : MvPolynomial (Fin N) K, f.totalDegree ≤ a+b → L f = 0 := by
  classical
  constructor
  · intro hz f hf
    rw [f.as_sum, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨u, v, hprod⟩ := split_monomial (K := K) a b d
      ((MvPolynomial.le_totalDegree hd).trans hf)
    have hm : L (MvPolynomial.monomial d 1) = 0 := by
      rw [hprod]
      exact congrFun (congrFun hz u) v
    have heq : MvPolynomial.monomial d (MvPolynomial.coeff d f) =
        (MvPolynomial.coeff d f) • MvPolynomial.monomial d (1 : K) := by
      simp [MvPolynomial.smul_monomial]
    rw [heq, map_smul, hm, smul_zero]
  · intro hz
    ext u v
    change L (monomialPolynomial u * monomialPolynomial v) = 0
    apply hz
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (monomial_degree_le u) (monomial_degree_le v))

/-- A truncated one-variable recurrence forces evaluation at the corresponding point. -/
theorem evaluation_of_recurrence {K : Type*} [Field K] {N : ℕ} (e : ℕ)
    (L : MvPolynomial (Fin N) K →ₗ[K] K) (point : Fin N → K)
    (hrec : ∀ (i : Fin N) (f : MvPolynomial (Fin N) K),
      f.totalDegree + 1 ≤ e → L (MvPolynomial.X i * f) = point i * L f) :
    ∀ f : MvPolynomial (Fin N) K, f.totalDegree ≤ e →
      L f = L 1 * MvPolynomial.eval point f := by
  classical
  have hm : ∀ (d : Fin N →₀ ℕ) (c : K),
      (MvPolynomial.monomial d c).totalDegree ≤ e →
      L (MvPolynomial.monomial d c) =
        L 1 * MvPolynomial.eval point (MvPolynomial.monomial d c) := by
    apply MvPolynomial.induction_on_monomial
      (motive := fun p : MvPolynomial (Fin N) K =>
        p.totalDegree ≤ e → L p = L 1 * MvPolynomial.eval point p)
    · intro c hc
      simpa [MvPolynomial.smul_eq_C_mul, mul_comm] using (L.map_smul c (1 : MvPolynomial (Fin N) K))
    · intro p i ih hpdeg
      by_cases hp : p = 0
      · simp [hp]
      have hdp : p.totalDegree + 1 ≤ e := by
        simpa [MvPolynomial.totalDegree_mul_of_isDomain hp (MvPolynomial.X_ne_zero i)] using hpdeg
      have hval := hrec i p hdp
      calc
        L (p * MvPolynomial.X i) = L (MvPolynomial.X i * p) := by rw [mul_comm]
        _ = point i * L p := hval
        _ = L 1 * MvPolynomial.eval point (p * MvPolynomial.X i) := by
          rw [ih (by omega)]
          simp [MvPolynomial.eval_mul, mul_left_comm, mul_comm, mul_assoc]
  intro f hf
  rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply hm
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    ((MvPolynomial.le_totalDegree hd).trans hf)

end SelectorProof

/-- Registered selector child, proved from bounded functional recurrences. -/
theorem rectangular_selector_nonzero :
  ∀ (K : Type*) [Field K] (N k a b : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hidentities : AnnihilatesEquations q L ((a+1)+(b+1)))
    (hne : rectangularTable (a+1) (b+1) L ≠ 0),
    ∃ i : Fin N,
      rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) ≠ 0 ∧
      rectangularTable (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) ≠ 0 := by
  intro K _ N k a b q hq hunsat L hidentities hne
  classical
  by_contra hsplit
  have hchoice : ∀ i : Fin N,
      rectangularTable a (b+1) (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0 ∨
      rectangularTable (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) = 0 := by
    intro i
    by_cases hx : rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0
    · exact Or.inl hx
    · apply Or.inr
      by_contra hc
      exact hsplit ⟨i, hx, hc⟩
  let assignment : BooleanAssignment N := fun i =>
    if rectangularTable a (b+1)
      (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0 then false else true
  have hrec : ∀ (i : Fin N) (f : MvPolynomial (Fin N) K),
      f.totalDegree + 1 ≤ (a+1)+(b+1) →
      L (MvPolynomial.X i * f) = booleanPoint assignment i * L f := by
    intro i f hf
    by_cases hx : rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0
    · have hsmall : f.totalDegree ≤ a+(b+1) := by omega
      have hz := (SelectorProof.table_zero_iff a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).mp hx f hsmall
      simpa [booleanPoint, assignment, hx] using hz
    · have hc := (hchoice i).resolve_left hx
      have hsmall : f.totalDegree ≤ (a+1)+b := by omega
      have hz := (SelectorProof.table_zero_iff (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).mp hc f hsmall
      change L ((1 - MvPolynomial.X i) * f) = 0 at hz
      have hsub : L f - L (MvPolynomial.X i * f) = 0 := by
        simpa [sub_mul, map_sub] using hz
      have hX : L (MvPolynomial.X i * f) = L f := (sub_eq_zero.mp hsub).symm
      simpa [booleanPoint, assignment, hx] using hX
  have hall := SelectorProof.evaluation_of_recurrence ((a+1)+(b+1)) L
    (booleanPoint assignment) hrec
  have hL1 : L 1 ≠ 0 := by
    intro hz
    apply hne
    apply (SelectorProof.table_zero_iff (a+1) (b+1) L).mpr
    intro f hf
    rw [hall f hf, hz, zero_mul]
  obtain ⟨s, hs⟩ := hunsat assignment
  have hzero : L (q s) = 0 := by
    have hh := (hidentities 1 (by simp; omega)).2 s
    simpa using hh
  have hdegree : (q s).totalDegree ≤ (a+1)+(b+1) := by have hh := hq s; omega
  have hmul : L 1 * MvPolynomial.eval (booleanPoint assignment) (q s) = 0 := by
    rw [← hall (q s) hdegree]
    exact hzero
  exact hs ((mul_eq_zero.mp hmul).resolve_left hL1)

end GenericGroupWE.Main



namespace GenericGroupWE.Main

/-- Generic rank-nullity ingredient for the proposed additive rank child. -/
theorem finrank_split_of_triple_comp_zero
    {K U V W T : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (h : U →ₗ[K] V) (p : V →ₗ[K] W) (q : T →ₗ[K] U)
    (hz : p.comp (h.comp q) = 0) :
    Module.finrank K (LinearMap.range (p.comp h)) +
      Module.finrank K (LinearMap.range (h.comp q)) ≤
      Module.finrank K (LinearMap.range h) := by
  let R := LinearMap.range h
  let pR := p.domRestrict R
  let qR : T →ₗ[K] R := (h.comp q).codRestrict R (fun x => ⟨q x, rfl⟩)
  have hpR : LinearMap.range pR = LinearMap.range (p.comp h) := by
    simp [pR, R, LinearMap.range_domRestrict, LinearMap.range_comp]
  have hqR : Module.finrank K (LinearMap.range (h.comp q)) =
      Module.finrank K (LinearMap.range qR) := by
    have heq : R.subtype.comp qR = h.comp q := by ext x; rfl
    rw [← heq, LinearMap.range_comp, Submodule.finrank_map_subtype_eq]
  have hsub : LinearMap.range qR ≤ LinearMap.ker pR := by
    rintro x ⟨y, rfl⟩
    change p (h (q y)) = 0
    exact congrArg (fun f : T →ₗ[K] W => f y) hz
  calc
    Module.finrank K (LinearMap.range (p.comp h)) +
        Module.finrank K (LinearMap.range (h.comp q)) =
        Module.finrank K (LinearMap.range pR) +
          Module.finrank K (LinearMap.range qR) := by rw [hpR, hqR]
    _ ≤ Module.finrank K (LinearMap.range pR) +
          Module.finrank K (LinearMap.ker pR) :=
      Nat.add_le_add_left (Submodule.finrank_mono hsub) _
    _ = Module.finrank K (LinearMap.range h) :=
      pR.finrank_range_add_finrank_ker


open scoped BigOperators

noncomputable def ordinaryIncl {N e : ℕ} (u : OrdinaryMonomial N e) :
    OrdinaryMonomial N (e+1) :=
  ⟨fun j => ⟨(u.val j).val, by have h := (u.val j).isLt; omega⟩,
    by simpa using u.property.trans (Nat.le_succ e)⟩

noncomputable def ordinaryRaise {N e : ℕ} (i : Fin N) (u : OrdinaryMonomial N e) :
    OrdinaryMonomial N (e+1) := by
  classical
  refine ⟨fun j => ⟨(u.val j).val + if j=i then 1 else 0, ?_⟩, ?_⟩
  · have h := (u.val j).isLt
    split_ifs <;> omega
  · change (∑ j : Fin N, ((u.val j).val + if j=i then 1 else 0)) ≤ e+1
    rw [Finset.sum_add_distrib]
    simpa using Nat.add_le_add_right u.property 1

theorem monomial_ordinaryIncl {K : Type*} [Field K] {N e : ℕ}
    (u : OrdinaryMonomial N e) :
    monomialPolynomial (K := K) (ordinaryIncl u) = monomialPolynomial u := by
  rfl

theorem monomial_ordinaryRaise {K : Type*} [Field K] {N e : ℕ}
    (i : Fin N) (u : OrdinaryMonomial N e) :
    monomialPolynomial (K := K) (ordinaryRaise i u) =
      MvPolynomial.X i * monomialPolynomial u := by
  classical
  have hexp :
      Finsupp.equivFunOnFinite.symm (fun j => ((ordinaryRaise i u).val j).val) =
      Finsupp.single i 1 + Finsupp.equivFunOnFinite.symm (fun j => (u.val j).val) := by
    ext j
    simp [ordinaryRaise, Finsupp.single_apply, eq_comm, add_comm]
  unfold monomialPolynomial
  change MvPolynomial.monomial _ (1 : K) =
    MvPolynomial.monomial (Finsupp.single i 1) 1 * MvPolynomial.monomial _ 1
  rw [MvPolynomial.monomial_mul, one_mul, hexp]

theorem monomial_totalDegree_le {K : Type*} [Field K] {N e : ℕ}
    (u : OrdinaryMonomial N e) :
    (monomialPolynomial (K := K) u).totalDegree ≤ e := by
  unfold monomialPolynomial
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  simpa [Finsupp.sum_fintype] using u.property

/-- Direct proof draft for the named registered child. -/
theorem rectangular_rank_split :
  ∀ (K : Type*) [Field K] (N a b : ℕ)
    (L : MvPolynomial (Fin N) K →ₗ[K] K) (i : Fin N)
    (hboolean : ∀ f : MvPolynomial (Fin N) K,
      f.totalDegree + 2 ≤ (a+1)+(b+1) →
      L (((MvPolynomial.X i)^2 - MvPolynomial.X i) * f) = 0),
    (rectangularTable a (b+1)
      (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).rank +
    (rectangularTable (a+1) b
      (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).rank ≤
    (rectangularTable (a+1) (b+1) L).rank := by
  intro K _ N a b L i hboolean
  classical
  let H : Matrix (OrdinaryMonomial N (a+1)) (OrdinaryMonomial N (b+1)) K :=
    rectangularTable (a+1) (b+1) L
  let P : Matrix (OrdinaryMonomial N a) (OrdinaryMonomial N (a+1)) K :=
    Matrix.of fun u w => if w = ordinaryRaise i u then 1 else 0
  let Q : Matrix (OrdinaryMonomial N (b+1)) (OrdinaryMonomial N b) K :=
    Matrix.of fun w v => (if w = ordinaryIncl v then 1 else 0) -
      (if w = ordinaryRaise i v then 1 else 0)
  have hPH : P * H = rectangularTable a (b+1)
      (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) := by
    ext u v
    change (∑ w, P u w * H w v) =
      L (MvPolynomial.X i * (monomialPolynomial u * monomialPolynomial v))
    simp [P, H, ite_mul, rectangularTable, monomial_ordinaryRaise, mul_assoc]
  have hHQ : H * Q = rectangularTable (a+1) b
      (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) := by
    ext u v
    change (∑ w, H u w * Q w v) =
      L ((1 - MvPolynomial.X i) * (monomialPolynomial u * monomialPolynomial v))
    simp only [Q, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change L (monomialPolynomial u * monomialPolynomial (ordinaryIncl v)) -
      L (monomialPolynomial u * monomialPolynomial (ordinaryRaise i v)) =
      L ((1 - MvPolynomial.X i) * (monomialPolynomial u * monomialPolynomial v))
    rw [monomial_ordinaryIncl, monomial_ordinaryRaise, ← map_sub]
    congr 1
    ring
  have hz : P * H * Q = 0 := by
    rw [Matrix.mul_assoc, hHQ]
    ext u v
    change (∑ w, P u w *
      L ((1 - MvPolynomial.X i) * (monomialPolynomial w * monomialPolynomial v))) = 0
    simp only [P, Matrix.of_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change L ((1 - MvPolynomial.X i) *
      (monomialPolynomial (ordinaryRaise i u) * monomialPolynomial v)) = 0
    rw [monomial_ordinaryRaise]
    have hdeg : (monomialPolynomial (K := K) u * monomialPolynomial v).totalDegree + 2 ≤
        (a+1)+(b+1) := by
      have hu := monomial_totalDegree_le (K := K) u
      have hv := monomial_totalDegree_le (K := K) v
      have hm := MvPolynomial.totalDegree_mul
        (monomialPolynomial (K := K) u) (monomialPolynomial (K := K) v)
      omega
    have hb := hboolean (monomialPolynomial u * monomialPolynomial v) hdeg
    have heq : (1 - MvPolynomial.X i) *
        ((MvPolynomial.X i * monomialPolynomial u) * monomialPolynomial v) =
        -(((MvPolynomial.X i)^2 - MvPolynomial.X i) *
          (monomialPolynomial (K := K) u * monomialPolynomial v)) := by ring
    rw [heq, map_neg, hb, neg_zero]
  have hcomp : P.mulVecLin.comp (H.mulVecLin.comp Q.mulVecLin) = 0 := by
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, ← Matrix.mul_assoc,
      hz, Matrix.mulVecLin_zero]
  have hr := finrank_split_of_triple_comp_zero H.mulVecLin P.mulVecLin Q.mulVecLin hcomp
  rw [Matrix.rank, Matrix.rank, Matrix.rank, ← hPH, ← hHQ,
    Matrix.mulVecLin_mul, Matrix.mulVecLin_mul]
  exact hr

end GenericGroupWE.Main




universe u

namespace GenericGroupWE.Main

/-- Provisional local helper; no changes to the canonical definitions. -/
theorem nonzero_matrix_rank_ge_one {K : Type*} [Field K]
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) (hne : A ≠ 0) :
    1 ≤ A.rank := by
  classical
  by_contra h
  have hr : A.rank = 0 := by omega
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at hr
  apply hne
  ext i j
  have hj : A.col j ∈ Submodule.span K (Set.range A.col) :=
    Submodule.subset_span (Set.mem_range_self j)
  rw [hr] at hj
  have hj0 : A.col j = 0 := hj
  exact congrFun hj0 i

/-- Multiplication by any affine polynomial costs one degree. -/
theorem annihilates_mul_affine {K : Type*} [Field K] {N k e : ℕ}
    (q : Fin k → MvPolynomial (Fin N) K)
    (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (p : MvPolynomial (Fin N) K) (hp : p.totalDegree ≤ 1)
    (h : AnnihilatesEquations q L (e+1)) :
    AnnihilatesEquations q (L.comp (LinearMap.mulLeft K p)) e := by
  intro f hf
  have hpf : (p*f).totalDegree + 2 ≤ e + 1 := by
    have hd := MvPolynomial.totalDegree_mul p f
    omega
  obtain ⟨hb, hq⟩ := h (p*f) hpf
  constructor
  · intro i
    change L (p * (((MvPolynomial.X i)^2 - MvPolynomial.X i) * f)) = 0
    convert hb i using 1 <;> congr 1 <;> ring
  · intro s
    change L (p * (q s * f)) = 0
    convert hq s using 1 <;> congr 1 <;> ring

/-- Completely closed base case for either zero side length. -/
theorem rectangular_zero_side {K : Type*} [Field K] {N : ℕ}
    (a b : ℕ) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hz : a = 0 ∨ b = 0) (hne : rectangularTable a b L ≠ 0) :
    Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := by
  have hr := nonzero_matrix_rank_ge_one (rectangularTable a b L) hne
  rcases hz with rfl | rfl
  · simpa using hr
  · simpa using hr

end GenericGroupWE.Main

namespace GenericGroupWE.Main

/-- Bounded direct proof of the induction, parameterized by provisional children. -/
theorem rectangular_from_splits
    (selector : ∀ (K : Type u) [Field K] (N k a b : ℕ)
      (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
      (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
      (hidentities : AnnihilatesEquations q L ((a+1)+(b+1)))
      (hne : rectangularTable (a+1) (b+1) L ≠ 0),
      ∃ i : Fin N,
        rectangularTable a (b+1)
          (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) ≠ 0 ∧
        rectangularTable (a+1) b
          (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) ≠ 0)
    (split : ∀ (K : Type u) [Field K] (N a b : ℕ)
      (L : MvPolynomial (Fin N) K →ₗ[K] K) (i : Fin N)
      (hboolean : ∀ f : MvPolynomial (Fin N) K,
        f.totalDegree + 2 ≤ (a+1)+(b+1) →
        L (((MvPolynomial.X i)^2 - MvPolynomial.X i) * f) = 0),
      (rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).rank +
      (rectangularTable (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).rank ≤
      (rectangularTable (a+1) (b+1) L).rank)
    (K : Type u) [Field K] (N k : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) :
    ∀ (a b : ℕ) (L : MvPolynomial (Fin N) K →ₗ[K] K)
      (hidentities : a ≠ 0 → b ≠ 0 → AnnihilatesEquations q L (a+b))
      (hne : rectangularTable a b L ≠ 0),
      Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := by
  intro a
  induction a with
  | zero =>
      intro b L hidentities hne
      exact rectangular_zero_side 0 b L (Or.inl rfl) hne
  | succ a ihA =>
      intro b
      induction b with
      | zero =>
          intro L hidentities hne
          exact rectangular_zero_side (a+1) 0 L (Or.inr rfl) hne
      | succ b ihB =>
          intro L hidentities hne
          have hAnn := hidentities (by omega) (by omega)
          obtain ⟨i, hx, h1x⟩ := selector K N k a b q hq hunsat L hAnn hne
          have hxAnn : AnnihilatesEquations q
              (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) (a+(b+1)) := by
            apply annihilates_mul_affine q L (MvPolynomial.X i) (by simp)
            convert hAnn using 1 <;> omega
          have h1xAnn : AnnihilatesEquations q
              (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) ((a+1)+b) := by
            apply annihilates_mul_affine q L (1 - MvPolynomial.X i)
            · exact (MvPolynomial.totalDegree_sub 1 (MvPolynomial.X i)).trans (by simp)
            · convert hAnn using 1 <;> omega
          have hxBound := ihA (b+1)
            (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) (fun _ _ => hxAnn) hx
          have h1xBound := ihB
            (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))
            (fun _ _ => h1xAnn) h1x
          calc
            Nat.choose ((a+1)+(b+1)) (a+1) =
                Nat.choose (a+(b+1)) a + Nat.choose ((a+1)+b) (a+1) := by
                  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.choose_succ_succ' (a+b+1) a)
            _ ≤ (rectangularTable a (b+1)
                  (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).rank +
                (rectangularTable (a+1) b
                  (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).rank :=
              Nat.add_le_add hxBound h1xBound
            _ ≤ (rectangularTable (a+1) (b+1) L).rank :=
              split K N a b L i (fun f hf => (hAnn f hf).1 i)

end GenericGroupWE.Main

namespace GenericGroupWE.Main

theorem lemma_6_2 (K : Type*) [Field K] (N k a b : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hidentities : a ≠ 0 → b ≠ 0 → AnnihilatesEquations q L (a+b))
    (hne : rectangularTable a b L ≠ 0) :
    Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := by
  exact rectangular_from_splits rectangular_selector_nonzero rectangular_rank_split
    K N k q hq hunsat a b L hidentities hne

end GenericGroupWE.Main

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
  ∀ (K : Type*) [Field K] (N k a b : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hidentities : a ≠ 0 → b ≠ 0 → AnnihilatesEquations q L (a+b))
    (hne : rectangularTable a b L ≠ 0),
Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := @GenericGroupWE.Main.lemma_6_2
