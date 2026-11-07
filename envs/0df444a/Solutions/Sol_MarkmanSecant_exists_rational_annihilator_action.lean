-- Prove2me | solution 1 for MarkmanSecant.exists_rational_annihilator_action
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T04:42:44.012112+00:00
-- url     : https://prove2.me/submissions/817e8b54-4352-4210-a6ba-a194f39bb920

import Mathlib
import Definitions.Def_MarkmanSecant

/-!
Rational descent of the secant annihilator action.
The exterior basis gives rational Clifford matrices. Solvability of a rational
linear system descends from C to Q by a separating-functional argument. The
complementary annihilators solve the joint system over C; rational solutions
for the standard basis give the desired rational matrix.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix

theorem linear_system_descent {K L : Type*} [Field K] [Field L]
    {m n : Type*} [Fintype m] [Fintype n]
    (φ : K →+* L) (A : Matrix m n K) (b : m → K)
    (h : ∃ x : n → L, (A.map φ).mulVec x = φ ∘ b) :
    ∃ x : n → K, A.mulVec x = b := by
  classical
  change b ∈ LinearMap.range A.mulVecLin
  by_contra hb
  obtain ⟨f, hfb, hfzero⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
  let w : m → K := fun i => f (Pi.single i 1)
  have hf (y : m → K) : f y = w ⬝ᵥ y := by
    have hr := congrArg f ((Pi.basisFun K m).sum_repr y)
    simpa [w, dotProduct, map_sum, map_smul, smul_eq_mul, mul_comm] using hr.symm
  have hfA (v : n → K) : f (A.mulVec v) = 0 := by
    have hv : f (A.mulVec v) ∈ (LinearMap.range A.mulVecLin).map f := by
      exact Submodule.mem_map.mpr ⟨A.mulVec v, ⟨v, rfl⟩, rfl⟩
    rwa [hfzero, Submodule.mem_bot] at hv
  have hwA : w ᵥ* A = 0 := by
    ext j
    have hj := hfA (Pi.single j 1)
    rw [hf] at hj
    simpa [Matrix.mulVec, Matrix.vecMul, dotProduct, Pi.single_apply] using hj
  obtain ⟨x, hx⟩ := h
  have hwAc : (φ ∘ w) ᵥ* A.map φ = 0 := by
    ext j
    rw [← RingHom.map_vecMul, hwA]
    simp
  have hz : φ (f b) = 0 := by
    rw [hf, RingHom.map_dotProduct, ← hx, dotProduct_mulVec, hwAc]
    simp
  exact hfb (φ.injective (by simpa using hz))



set_option backward.isDefEq.respectTransparency false

open MarkmanSecant
open scoped ExteriorAlgebra

noncomputable section

namespace MarkmanRationalCoordinates

def spinBasis (n : ℕ) : Module.Basis (Finset (Fin (2 * n))) ℂ (Spinor n) :=
  (Pi.basisFun ℂ (Fin (2 * n))).ExteriorAlgebra

def ratSpan (n : ℕ) : Submodule ℚ (Spinor n) :=
  Submodule.span ℚ (Set.range (spinBasis n))

lemma basis_mem (n : ℕ) (s : Finset (Fin (2 * n))) : spinBasis n s ∈ ratSpan n :=
  Submodule.subset_span (Set.mem_range_self s)

lemma basis_empty (n : ℕ) : spinBasis n ∅ = 1 := by
  simp [spinBasis, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family]

lemma basis_singleton (n : ℕ) (i : Fin (2 * n)) :
    spinBasis n {i} = ExteriorAlgebra.ι ℂ (Pi.single i 1) := by
  rw [spinBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    Set.powersetCard.ofCard, Set.powersetCard.ofFinEmbEquiv, Finset.orderEmbOfFin_singleton]

lemma basis_mul_mem (n : ℕ) (s t : Finset (Fin (2 * n))) :
    spinBasis n s * spinBasis n t ∈ ratSpan n := by
  classical
  let s' : Set.powersetCard (Fin (2 * n)) s.card := ⟨s, rfl⟩
  let t' : Set.powersetCard (Fin (2 * n)) t.card := ⟨t, rfl⟩
  by_cases h : Disjoint s t
  · have he := ExteriorAlgebra.basis_mul_of_disjoint
      (Pi.basisFun ℂ (Fin (2 * n))) s' t' h
    change _ ∈ ratSpan n
    rw [show spinBasis n s * spinBasis n t = _ from he]
    exact (ratSpan n).toAddSubgroup.zsmul_mem (basis_mem n _) _
  · have he := ExteriorAlgebra.basis_mul_of_not_disjoint
      (Pi.basisFun ℂ (Fin (2 * n))) s' t' h
    rw [show spinBasis n s * spinBasis n t = 0 from he]
    exact (ratSpan n).zero_mem

lemma mul_mem (n : ℕ) (x y : Spinor n) (hx : x ∈ ratSpan n) (hy : y ∈ ratSpan n) :
    x * y ∈ ratSpan n := by
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨t, rfl⟩ := hy; exact basis_mul_mem n s t
    | zero => simpa using (ratSpan n).zero_mem
    | add y z _ _ hy hz => simpa [mul_add] using (ratSpan n).add_mem hy hz
    | smul c y _ hy => simpa [mul_smul_comm] using (ratSpan n).smul_mem c hy
  | zero => simpa using (ratSpan n).zero_mem
  | add x z _ _ hx hz => simpa [add_mul] using (ratSpan n).add_mem (hx y hy) (hz y hy)
  | smul c x _ hx => simpa [smul_mul_assoc] using (ratSpan n).smul_mem c (hx y hy)

lemma monomial_mem (n : ℕ) (l : List (Fin (2 * n))) : monomial l ∈ ratSpan n := by
  induction l with
  | nil => simpa [monomial, basis_empty] using basis_mem n ∅
  | cons i l ih =>
    simpa [monomial] using mul_mem n (ExteriorAlgebra.ι ℂ (Pi.single i 1)) (monomial l)
      (by rw [← basis_singleton]; exact basis_mem n {i}) ih

lemma integral_mem (n : ℕ) (s : Spinor n) (hs : IsIntegralClass s) : s ∈ ratSpan n := by
  induction hs using Submodule.span_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact monomial_mem n l
  | zero => exact (ratSpan n).zero_mem
  | add x y _ _ hx hy => exact (ratSpan n).add_mem hx hy
  | smul c x _ hx => exact (ratSpan n).toAddSubgroup.zsmul_mem hx c

lemma rational_mem (n : ℕ) (s : Spinor n) (hs : IsRationalClass s) : s ∈ ratSpan n := by
  obtain ⟨m, hm, hs⟩ := hs
  have h := (ratSpan n).smul_mem ((m : ℚ)⁻¹) (integral_mem n _ hs)
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hcast : ((m : ℚ)⁻¹) • ((m : ℂ) • s) = ((m : ℂ)⁻¹) • ((m : ℂ) • s) := by
    simpa using ratCast_smul_eq ℚ ℂ ((m : ℚ)⁻¹) ((m : ℂ) • s)
  rw [hcast, smul_smul, inv_mul_cancel₀ hm0, one_smul] at h
  exact h

lemma basis_is_monomial (n : ℕ) (s : Finset (Fin (2 * n))) :
    ∃ l : List (Fin (2 * n)), spinBasis n s = monomial l := by
  rw [spinBasis, ExteriorAlgebra.basis_apply]
  refine ⟨List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.prodEquiv.symm s).2), ?_⟩
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    monomial, List.map_ofFn, Function.comp_def, Pi.basisFun_apply]

lemma dual_single (n : ℕ) (i j : Fin (2 * n)) :
    dualOf (Pi.single i 1) (Pi.single j 1) = if i = j then (1 : ℂ) else 0 := by
  classical
  simp [dualOf, dualLin, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Pi.single_apply]

lemma contract_monomial_mem (n : ℕ) (j : Fin (2 * n)) (l : List (Fin (2 * n))) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))
      (dualOf (Pi.single j 1)) (monomial l) ∈ ratSpan n := by
  classical
  induction l with
  | nil => simp [monomial]
  | cons i l ih =>
    change CliffordAlgebra.contractLeft (dualOf (Pi.single j 1))
      (ExteriorAlgebra.ι ℂ (Pi.single i 1) * monomial l) ∈ ratSpan n
    rw [CliffordAlgebra.contractLeft_ι_mul, dual_single]
    have hprod := mul_mem n (ExteriorAlgebra.ι ℂ (Pi.single i 1)) _
      (by rw [← basis_singleton]; exact basis_mem n {i}) ih
    apply (ratSpan n).sub_mem
    · split_ifs <;> simp [monomial_mem]
    · exact hprod

lemma contract_mem (n : ℕ) (j : Fin (2 * n)) (s : Spinor n) (hs : s ∈ ratSpan n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))
      (dualOf (Pi.single j 1)) s ∈ ratSpan n := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨l, hl⟩ := basis_is_monomial n s
    rw [hl]
    exact contract_monomial_mem n j l
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (ratSpan n).add_mem hx hy
  | smul c x _ hx =>
    simpa only [LinearMap.map_smul_of_tower] using (ratSpan n).smul_mem c hx

lemma cliff_single_mem (n : ℕ) (s : Spinor n) (hs : s ∈ ratSpan n) (j : VIdx n) :
    cliffAt s (Pi.single j 1) ∈ ratSpan n := by
  classical
  change ExteriorAlgebra.ι ℂ (wPart (Pi.single j 1)) * s +
    CliffordAlgebra.contractLeft (dualOf (tPart (Pi.single j 1))) s ∈ ratSpan n
  cases j with
  | inl j =>
    have hw : wPart (Pi.single (Sum.inl j) (1 : ℂ)) = Pi.single j 1 := by
      ext i
      simp [wPart, Pi.single_apply]
    have ht : tPart (Pi.single (Sum.inl j) (1 : ℂ)) = 0 := by
      ext i
      simp [tPart, Pi.single_apply]
    rw [hw, ht]
    simp only [dualOf, map_zero, LinearMap.zero_apply, add_zero]
    exact mul_mem n _ s (by rw [← basis_singleton]; exact basis_mem n {j}) hs
  | inr j =>
    have hw : wPart (Pi.single (Sum.inr j) (1 : ℂ)) = 0 := by
      ext i
      simp [wPart, Pi.single_apply]
    have ht : tPart (Pi.single (Sum.inr j) (1 : ℂ)) = Pi.single j 1 := by
      ext i
      simp [tPart, Pi.single_apply]
    rw [hw, ht, map_zero, zero_mul, zero_add]
    exact contract_mem n j s hs

def cliffMatrix (n : ℕ) (s : Spinor n) :
    Matrix (Finset (Fin (2 * n))) (VIdx n) ℂ :=
  LinearMap.toMatrix' ((spinBasis n).equivFun.toLinearMap ∘ₗ cliffAt s)

lemma rational_cliffMatrix (n : ℕ) (s : Spinor n) (hs : IsRationalClass s) :
    ∃ M : Matrix (Finset (Fin (2 * n))) (VIdx n) ℚ,
      M.map (algebraMap ℚ ℂ) = cliffMatrix n s := by
  classical
  have hc (i : Finset (Fin (2 * n))) (j : VIdx n) :
      ∃ q : ℚ, (q : ℂ) = cliffMatrix n s i j := by
    have hm := cliff_single_mem n s (rational_mem n s hs) j
    have hh := ((spinBasis n).mem_span_iff_repr_mem ℚ _).mp hm i
    simpa [cliffMatrix, LinearMap.toMatrix'_apply, Module.Basis.equivFun_apply] using hh
  choose M hM using hc
  refine ⟨M, ?_⟩
  ext i j
  exact hM i j


end MarkmanRationalCoordinates


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant MarkmanRationalCoordinates Matrix

noncomputable section

namespace MarkmanRationalAction

lemma cliff_apply {n : ℕ} (s : Spinor n) (v : VC n) :
    cliffAt s v = ExteriorAlgebra.ι ℂ (wPart v) * s +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))
        (dualOf (tPart v)) s := rfl

lemma cliff_add {n : ℕ} (a b : Spinor n) (v : VC n) :
    cliffAt (a + b) v = cliffAt a v + cliffAt b v := by
  simp only [cliff_apply, mul_add, map_add]
  abel

lemma cliff_sub {n : ℕ} (a b : Spinor n) (v : VC n) :
    cliffAt (a - b) v = cliffAt a v - cliffAt b v := by
  simp only [cliff_apply, mul_sub, map_sub]
  abel

lemma cliff_smul {n : ℕ} (c : ℂ) (a : Spinor n) (v : VC n) :
    cliffAt (c • a) v = c • cliffAt a v := by
  simp only [cliff_apply, mul_smul_comm, map_smul, smul_add]

lemma sqrtNeg_sq (d : ℚ) (hd : 0 < d) : (sqrtNeg d) ^ 2 = -(d : ℂ) := by
  unfold sqrtNeg
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (show 0 ≤ (d : ℝ) by exact_mod_cast hd.le)]
  push_cast
  ring

lemma complex_joint_solution (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b))
    (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (v : VC n) :
    ∃ u : VC n, cliffAt a u = (d : ℂ) • cliffAt b v ∧
      cliffAt b u = -cliffAt a v := by
  let c := sqrtNeg d
  have hcc : c * c = -(d : ℂ) := by simpa [pow_two, c] using sqrtNeg_sq d hd
  have hdim : Module.finrank ℂ (VC n) = 2 * n + 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hsup : annih (a + c • b) ⊔ annih (a - c • b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (annih (a + c • b)) (annih (a - c • b))
    rw [h₁₂, finrank_bot, h₁.2.2, h₂.2.2] at h
    rw [hdim]
    omega
  have hv : v ∈ annih (a + c • b) ⊔ annih (a - c • b) := by rw [hsup]; trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  have hpx : cliffAt a x = (-c) • cliffAt b x := by
    have h : cliffAt (a + c • b) x = 0 := hx
    rw [cliff_add, cliff_smul] at h
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left h
  have hmy : cliffAt a y = c • cliffAt b y := by
    have h : cliffAt (a - c • b) y = 0 := hy
    rw [cliff_sub, cliff_smul, sub_eq_zero] at h
    exact h
  refine ⟨c • x - c • y, ?_, ?_⟩
  · simp only [map_sub, map_smul, hpx, hmy, smul_neg, smul_smul,
      hcc, neg_neg, map_add, smul_add, neg_smul, sub_neg_eq_add]
  · simp only [map_sub, map_smul, map_add, hpx, hmy, neg_smul]
    abel

lemma rational_pair_solution {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℚ) (d : ℚ) (v : J → ℚ)
    (h : ∃ u : J → ℂ,
      (A.map (algebraMap ℚ ℂ)).mulVec u =
        (d : ℂ) • (B.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ)) ∧
      (B.map (algebraMap ℚ ℂ)).mulVec u =
        -(A.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ))) :
    ∃ u : J → ℚ, A.mulVec u = d • B.mulVec v ∧ B.mulVec u = -A.mulVec v := by
  let C := Matrix.fromRows A B
  let w : I ⊕ I → ℚ := Sum.elim (d • B.mulVec v) (-A.mulVec v)
  have hc : ∃ u : J → ℂ, (C.map (algebraMap ℚ ℂ)).mulVec u =
      (algebraMap ℚ ℂ) ∘ w := by
    obtain ⟨u, hu, hv⟩ := h
    refine ⟨u, ?_⟩
    ext i
    cases i with
    | inl i =>
      have hh := congrFun hu i
      simpa [C, w, Matrix.fromRows_map, Matrix.fromRows_mulVec,
        Matrix.mulVec, dotProduct, Function.comp_def] using hh
    | inr i =>
      have hh := congrFun hv i
      simpa [C, w, Matrix.fromRows_map, Matrix.fromRows_mulVec,
        Matrix.mulVec, dotProduct, Function.comp_def] using hh
  obtain ⟨u, hu⟩ := linear_system_descent (algebraMap ℚ ℂ) C w hc
  refine ⟨u, ?_, ?_⟩
  · funext i
    exact congrFun hu (Sum.inl i)
  · funext i
    exact congrFun hu (Sum.inr i)

lemma cliffMatrix_mulVec (n : ℕ) (s : Spinor n) (v : VC n) :
    (cliffMatrix n s).mulVec v = (spinBasis n).equivFun (cliffAt s v) := by
  simp [cliffMatrix, LinearMap.toMatrix'_mulVec]

lemma rational_matrix_solution {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℚ) (d : ℚ)
    (h : ∀ v : J → ℚ, ∃ u : J → ℂ,
      (A.map (algebraMap ℚ ℂ)).mulVec u =
        (d : ℂ) • (B.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ)) ∧
      (B.map (algebraMap ℚ ℂ)).mulVec u =
        -(A.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ))) :
    ∃ F : Matrix J J ℚ, A * F = d • B ∧ B * F = -A := by
  classical
  have hj (j : J) := rational_pair_solution A B d (Pi.single j 1) (h _)
  choose u hu using hj
  let F : Matrix J J ℚ := fun i j => u j i
  refine ⟨F, ?_, ?_⟩
  · ext i j
    have hh := congrFun (hu j).1 i
    simpa [Matrix.mulVec_single_one, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      F, Pi.single_apply] using hh
  · ext i j
    have hh := congrFun (hu j).2 i
    simpa [Matrix.mulVec_single_one, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      F, Pi.single_apply] using hh

lemma exists_joint_matrix (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsRationalClass a) (hb : IsRationalClass b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b))
    (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥) :
    ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
      (cliffMatrix n a) * ratMatV F = (d : ℂ) • cliffMatrix n b ∧
      (cliffMatrix n b) * ratMatV F = -cliffMatrix n a := by
  classical
  obtain ⟨A, hA⟩ := rational_cliffMatrix n a ha
  obtain ⟨B, hB⟩ := rational_cliffMatrix n b hb
  have h (v : VIdx n → ℚ) : ∃ u : VC n,
      (A.map (algebraMap ℚ ℂ)).mulVec u =
        (d : ℂ) • (B.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ)) ∧
      (B.map (algebraMap ℚ ℂ)).mulVec u =
        -(A.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ)) := by
    obtain ⟨u, hu, hv⟩ := complex_joint_solution n d hd a b h₁ h₂ h₁₂ (fun j => (v j : ℂ))
    refine ⟨u, ?_, ?_⟩
    · rw [hA, hB, cliffMatrix_mulVec, cliffMatrix_mulVec]
      simpa only [map_smul, ratV] using congrArg (spinBasis n).equivFun hu
    · rw [hA, hB, cliffMatrix_mulVec, cliffMatrix_mulVec]
      simpa only [map_neg, ratV] using congrArg (spinBasis n).equivFun hv
  obtain ⟨F, hF, hG⟩ := rational_matrix_solution A B d h
  refine ⟨F, ?_, ?_⟩
  · rw [← hA, ← hB]
    have hh := congrArg (fun M : Matrix _ _ ℚ => M.map (algebraMap ℚ ℂ)) hF
    ext i j
    simpa [ratMatV, Matrix.mul_apply, Matrix.map_apply] using congrFun (congrFun hh i) j
  · rw [← hA, ← hB]
    have hh := congrArg (fun M : Matrix _ _ ℚ => M.map (algebraMap ℚ ℂ)) hG
    ext i j
    simpa [ratMatV, Matrix.mul_apply, Matrix.map_apply] using congrFun (congrFun hh i) j

lemma joint_zero (n : ℕ) (d : ℚ) (a b : Spinor n)
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (v : VC n) (ha : cliffAt a v = 0) (hb : cliffAt b v = 0) : v = 0 := by
  have hv : v ∈ annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) := by
    constructor
    · change cliffAt (a + sqrtNeg d • b) v = 0
      simp [cliff_add, cliff_smul, ha, hb]
    · change cliffAt (a - sqrtNeg d • b) v = 0
      simp [cliff_sub, cliff_smul, ha, hb]
  rwa [h₁₂, Submodule.mem_bot] at hv

lemma action_of_joint (n : ℕ) (d : ℚ) (a b : Spinor n)
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (f : VC n →ₗ[ℂ] VC n)
    (hfa : ∀ v, cliffAt a (f v) = (d : ℂ) • cliffAt b v)
    (hfb : ∀ v, cliffAt b (f v) = -cliffAt a v)
    (c : ℂ) (hc : c * c = -(d : ℂ))
    (v : VC n) (hv : cliffAt a v = (-c) • cliffAt b v) : f v = c • v := by
  apply sub_eq_zero.mp
  apply joint_zero n d a b h₁₂
  · simp only [map_sub, map_smul, hfa, hv]
    rw [smul_smul, mul_neg, hc, neg_neg, sub_self]
  · simp [hfb, hv]

theorem rational_action (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsRationalClass a) (hb : IsRationalClass b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b))
    (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥) :
    ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
      (∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v) ∧
      (∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) := by
  obtain ⟨F, hF, hG⟩ := exists_joint_matrix n d hd a b ha hb h₁ h₂ h₁₂
  let f := Matrix.toLin' (ratMatV F)
  have hfa (v : VC n) : cliffAt a (f v) = (d : ℂ) • cliffAt b v := by
    apply (spinBasis n).equivFun.injective
    rw [map_smul, ← cliffMatrix_mulVec, ← cliffMatrix_mulVec]
    change (cliffMatrix n a).mulVec ((ratMatV F).mulVec v) = _
    rw [Matrix.mulVec_mulVec, hF, Matrix.smul_mulVec]
  have hfb (v : VC n) : cliffAt b (f v) = -cliffAt a v := by
    apply (spinBasis n).equivFun.injective
    rw [map_neg, ← cliffMatrix_mulVec, ← cliffMatrix_mulVec]
    change (cliffMatrix n b).mulVec ((ratMatV F).mulVec v) = _
    rw [Matrix.mulVec_mulVec, hG, Matrix.neg_mulVec]
  have hc : sqrtNeg d * sqrtNeg d = -(d : ℂ) := by
    simpa only [pow_two] using sqrtNeg_sq d hd
  refine ⟨F, ?_, ?_⟩
  · intro v hv
    apply action_of_joint n d a b h₁₂ f hfa hfb (sqrtNeg d) hc
    change cliffAt (a + sqrtNeg d • b) v = 0 at hv
    rw [cliff_add, cliff_smul] at hv
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hv
  · intro v hv
    apply action_of_joint n d a b h₁₂ f hfa hfb (-sqrtNeg d) (by simpa using hc)
    change cliffAt (a - sqrtNeg d • b) v = 0 at hv
    rw [cliff_sub, cliff_smul, sub_eq_zero] at hv
    simpa only [neg_neg] using hv


end MarkmanRationalAction

theorem solution (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsRationalClass a) (hb : IsRationalClass b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥) :
    ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
      (∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v) ∧
      (∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) := by
  exact MarkmanRationalAction.rational_action n d hd a b ha hb h₁ h₂ h₁₂

#print axioms solution
