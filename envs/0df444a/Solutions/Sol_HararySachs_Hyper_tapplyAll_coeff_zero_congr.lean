-- Prove2me | solution 1 for HararySachs.Hyper.tapplyAll_coeff_zero_congr
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T04:59:21.868129+00:00
-- url     : https://prove2.me/submissions/6cdb1dcc-2d57-4e4a-9154-d6975b919658

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

open HararySachs.Hyper MvPolynomial Finset

set_option linter.unusedSectionVars false

namespace TApplyAux

variable {n : ℕ}

/-! ### Linear-map form of the operators -/

/-- `∂_{(i,l₁)} ⋯ ∂_{(i,l_m)}` as an endomorphism -/
noncomputable def wordL (i : Fin n) (l : List (Fin n)) : Module.End ℚ (AuxPoly n) :=
  l.foldr (fun j L => (pderiv (i, j)).toLinearMap * L) 1

lemma wordL_apply (i : Fin n) (l : List (Fin n)) (p : AuxPoly n) :
    l.foldr (fun j q => pderiv (i, j) q) p = wordL i l p := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, wordL] at ih ⊢
    rw [ih]; rfl

variable {k : ℕ}

/-- `tfhat` as an endomorphism -/
noncomputable def fhL (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n) :
    Module.End ℚ (AuxPoly n) :=
  ∑ t : Fin (k - 1) → Fin n, A i t • wordL i (List.ofFn t)

lemma tfhat_eq (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n) :
    tfhat (k := k) A i = ⇑(fhL A i) := by
  funext p
  simp [tfhat, fhL, LinearMap.sum_apply, wordL_apply]

lemma iterate_eq (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n) (m : ℕ) :
    (tfhat (k := k) A i)^[m] = ⇑(fhL A i ^ m) := by
  rw [Module.End.coe_pow, tfhat_eq]

/-- `tapplyAll` as an endomorphism -/
noncomputable def applyL {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ)
    (a : Fin n → Fin (d + 1)) : Module.End ℚ (AuxPoly n) :=
  (List.ofFn (fun i : Fin n => i)).foldl (fun L i => fhL A i ^ (a i).val * L) 1

lemma foldl_apply {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (a : Fin n → Fin (d + 1))
    (l : List (Fin n)) (L : Module.End ℚ (AuxPoly n)) (p : AuxPoly n) :
    l.foldl (fun q i => ((tfhat (k := k) A i)^[(a i).val]) q) (L p) =
      (l.foldl (fun L i => fhL A i ^ (a i).val * L) L) p := by
  induction l generalizing L with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [← ih, iterate_eq]; rfl

lemma tapplyAll_eq {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (a : Fin n → Fin (d + 1))
    (p : AuxPoly n) : tapplyAll (k := k) A a p = applyL A a p := by
  have := foldl_apply A a (List.ofFn (fun i : Fin n => i)) 1 p
  simpa [tapplyAll, applyL] using this

/-! ### The row-degree grading (with values in `ℤⁿ`) -/

/-- the row-degree weight of a variable `V_{ij}` -/
def rw (v : Fin n × Fin n) : Fin n → ℤ := Pi.single v.1 1

/-- polynomials of row-degree vector `D` -/
abbrev S (D : Fin n → ℤ) : Submodule ℚ (AuxPoly n) :=
  weightedHomogeneousSubmodule ℚ (rw (n := n)) D

lemma weight_single_rw (v : Fin n × Fin n) :
    Finsupp.weight rw (Finsupp.single v 1) = rw v := by
  rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp), one_smul]

lemma weight_rw_apply (ν : Fin n × Fin n →₀ ℕ) (i : Fin n) :
    Finsupp.weight rw ν i = ∑ j, (ν (i, j) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp [rw, Pi.single_apply]

lemma pderiv_mem {D : Fin n → ℤ} {f : AuxPoly n} (hf : f ∈ S D) (v : Fin n × Fin n) :
    pderiv v f ∈ S (D - rw v) := by
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  intro ν hν
  rw [coeff_pderiv] at hν
  have h1 := hf (left_ne_zero_of_mul hν)
  rw [map_add, weight_single_rw] at h1
  rw [← h1]; abel

lemma wordL_mem (i : Fin n) (l : List (Fin n)) {D : Fin n → ℤ} {f : AuxPoly n}
    (hf : f ∈ S D) :
    wordL i l f ∈ S (D - (l.length : ℤ) • (Pi.single i 1 : Fin n → ℤ)) := by
  induction l with
  | nil => simpa [wordL] using hf
  | cons j l ih =>
    have h : wordL i (j :: l) f = pderiv (i, j) (wordL i l f) := rfl
    rw [h]
    have := pderiv_mem ih (i, j)
    convert this using 2
    simp only [List.length_cons, Nat.cast_succ, add_smul, one_smul, rw]
    abel

lemma fhL_mem (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n) {D : Fin n → ℤ}
    {f : AuxPoly n} (hf : f ∈ S D) :
    fhL A i f ∈ S (D - ((k - 1 : ℕ) : ℤ) • (Pi.single i 1 : Fin n → ℤ)) := by
  rw [fhL, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have := wordL_mem i (List.ofFn t) hf
  rwa [List.length_ofFn] at this

lemma fhL_pow_mem (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n) (m : ℕ)
    {D : Fin n → ℤ} {f : AuxPoly n} (hf : f ∈ S D) :
    (fhL A i ^ m) f ∈ S (D - ((m * (k - 1) : ℕ) : ℤ) • (Pi.single i 1 : Fin n → ℤ)) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := fhL_mem A i ih
    convert this using 2
    push_cast
    rw [add_mul, one_mul, add_smul]
    abel

lemma foldl_mem {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (a : Fin n → Fin (d + 1))
    (l : List (Fin n)) (L : Module.End ℚ (AuxPoly n)) (E : Fin n → ℤ)
    (hL : ∀ (D : Fin n → ℤ) (f : AuxPoly n), f ∈ S D → L f ∈ S (D - E)) :
    ∀ (D : Fin n → ℤ) (f : AuxPoly n), f ∈ S D →
      (l.foldl (fun L i => fhL A i ^ (a i).val * L) L) f ∈
        S (D - E - List.sum (l.map (fun i =>
          (((a i).val * (k - 1) : ℕ) : ℤ) • (Pi.single i 1 : Fin n → ℤ)))) := by
  induction l generalizing L E with
  | nil => intro D f hf; simpa using hL D f hf
  | cons j l ih =>
    intro D f hf
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have := ih (fhL A j ^ (a j).val * L)
      (E + (((a j).val * (k - 1) : ℕ) : ℤ) • (Pi.single j 1 : Fin n → ℤ))
      (fun D f hf => by
        rw [Module.End.mul_apply]
        have h2 := fhL_pow_mem A j (a j).val (hL D f hf)
        convert h2 using 2
        abel) D f hf
    convert this using 2
    abel

/-- the total shift of `applyL` -/
lemma applyL_mem {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (a : Fin n → Fin (d + 1))
    {D : Fin n → ℤ} {f : AuxPoly n} (hf : f ∈ S D) :
    applyL A a f ∈ S (D - fun i => (((a i).val * (k - 1) : ℕ) : ℤ)) := by
  have := foldl_mem A a (List.ofFn (fun i : Fin n => i)) 1 0 (fun D f hf => by simpa using hf)
    D f hf
  rw [List.map_ofFn, List.sum_ofFn, sub_zero] at this
  convert this using 2
  · ext i
    simp [Finset.sum_apply, Pi.single_apply]
  · rfl

lemma coeff_zero_applyL_monomial {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ)
    (a : Fin n → Fin (d + 1)) (ν : Fin n × Fin n →₀ ℕ) (c : ℚ)
    (hν : Finsupp.weight rw ν ≠ fun i => (((a i).val * (k - 1) : ℕ) : ℤ)) :
    coeff 0 (applyL A a (monomial ν c)) = 0 := by
  have hm : monomial ν c ∈ S (Finsupp.weight rw ν) := by
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_monomial _ _ _ rfl
  have h := applyL_mem A a hm
  rw [mem_weightedHomogeneousSubmodule] at h
  by_contra hne
  have h0 := h hne
  rw [map_zero] at h0
  exact hν (sub_eq_zero.mp h0.symm)

end TApplyAux

open TApplyAux in
theorem solution {n k d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ)
    (a : Fin n → Fin (d + 1)) (p q : AuxPoly n) (c : ℚ)
    (h : ∀ μ : Fin n × Fin n →₀ ℕ, (∀ i, ∑ j, μ (i, j) = (k - 1) * (a i).val) →
      MvPolynomial.coeff μ p = c * MvPolynomial.coeff μ q) :
    MvPolynomial.coeff 0 (tapplyAll (k := k) A a p) =
      c * MvPolynomial.coeff 0 (tapplyAll (k := k) A a q) := by
  classical
  rw [tapplyAll_eq, tapplyAll_eq, ← sub_eq_zero, ← smul_eq_mul, ← coeff_smul, ← coeff_sub,
    ← map_smul, ← map_sub]
  set f := p - c • q with hf
  rw [f.as_sum, map_sum, coeff_sum]
  refine sum_eq_zero fun ν hν => ?_
  by_cases hw : Finsupp.weight rw ν = fun i => (((a i).val * (k - 1) : ℕ) : ℤ)
  · exfalso
    rw [mem_support_iff] at hν
    apply hν
    have hrow : ∀ i, ∑ j, ν (i, j) = (k - 1) * (a i).val := by
      intro i
      have := congrFun hw i
      rw [weight_rw_apply] at this
      rw [mul_comm]
      exact_mod_cast this
    rw [hf, coeff_sub, coeff_smul, h ν hrow, smul_eq_mul, sub_self]
  · exact coeff_zero_applyL_monomial A a ν _ hw
