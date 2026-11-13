-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_row_invariance
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:07:08.060328+00:00
-- url     : https://prove2.me/submissions/c97defda-6813-4fee-8b1d-3d5d4d3cc1f6

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Theorems.Thm_HararySachs_Hyper_newtonTr_generic_row_invariance

open HararySachs.Hyper MvPolynomial Finset

set_option linter.unusedSectionVars false

namespace RowSpecAux

/-! ### Naturality of `phiPoly` and `newtonTr` under ring homomorphisms -/

section Naturality

variable {R S : Type*} [CommRing R] [CommRing S] {n k : ℕ}

lemma zcoord_map (f : R →+* S) (A : Fin n → (Fin (k - 1) → Fin n) → R) (j : Fin n) :
    zcoord (k := k) (fun i t => f (A i t)) j =
      MvPolynomial.map (Polynomial.mapRingHom f) (zcoord (k := k) A j) := by
  simp [zcoord, map_sub, map_sum, MvPolynomial.map_monomial]

lemma phiPoly_map (f : R →+* S) (A : Fin n → (Fin (k - 1) → Fin n) → R)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) :
    phiPoly (k := k) (fun i t => f (A i t)) res = (phiPoly (k := k) A res).map f := by
  unfold phiPoly
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext v
    simp only [Function.comp_apply, zcoord_map, MvPolynomial.coeff_map]

lemma newtonTr_map (f : R →+* S) (Φ : Polynomial R) (d : ℕ) :
    newtonTr (Φ.map f) d = f (newtonTr Φ d) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => simp [newtonTr]
    | succ d =>
      rw [newtonTr, newtonTr, map_sub, map_neg, map_mul, map_sum, map_natCast,
        Polynomial.coeff_map]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [map_mul, ih j (by omega), Polynomial.coeff_map]

lemma newtonTr_phiPoly_map (f : R →+* S) (A : Fin n → (Fin (k - 1) → Fin n) → R)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (d : ℕ) :
    newtonTr (phiPoly (k := k) (fun i t => f (A i t)) res) d =
      f (newtonTr (phiPoly (k := k) A res) d) := by
  rw [phiPoly_map, newtonTr_map]

end Naturality

/-! ### Polynomials free of the row-`i` variables -/

variable {n : ℕ}

/-- set the variables of row `i` to zero -/
noncomputable def Z (i : Fin n) : AuxPoly n →ₐ[ℚ] AuxPoly n :=
  aeval (fun v : Fin n × Fin n => if v.1 = i then (0 : AuxPoly n) else X v)

lemma Z_of_free (i : Fin n) {p : AuxPoly n} (hp : ∀ v ∈ p.vars, v.1 ≠ i) : Z i p = p := by
  have := MvPolynomial.hom_congr_vars (f₁ := (Z i).toRingHom) (f₂ := RingHom.id _)
    (p₁ := p) (p₂ := p) (by ext; simp [Z]) (fun v hv => by simp [Z, hp v hv]) rfl
  simpa using this

lemma pderiv_of_free (i l : Fin n) {p : AuxPoly n} (hp : ∀ v ∈ p.vars, v.1 ≠ i) :
    pderiv (i, l) p = 0 :=
  pderiv_eq_zero_of_notMem_vars fun h => hp _ h rfl

variable {k : ℕ}

/-- the generic coefficient ring -/
abbrev Rg (n k : ℕ) := MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ

/-- specialise the generic tensor to `A` -/
noncomputable def psi (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n) : Rg n k →ₐ[ℚ] AuxPoly n :=
  aeval (fun p => A p.1 p.2)

lemma psi_X (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n) (j : Fin n) (t : Fin (k - 1) → Fin n) :
    psi A (X (j, t)) = A j t := by
  simp [psi]

lemma psi_C (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n) (a : ℚ) :
    psi A (C a) = C a := by
  simp [psi, MvPolynomial.algebraMap_eq]

/-- specialise the generic tensor to `A` and the `v`-variables to row `i` of `V` -/
noncomputable def psiv (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n) (i : Fin n) :
    MvPolynomial (Fin n) (Rg n k) →+* AuxPoly n :=
  eval₂Hom ((psi A : Rg n k →ₐ[ℚ] AuxPoly n) : Rg n k →+* AuxPoly n) (fun l => X (i, l))

lemma psiv_C (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n) (i : Fin n) (c : Rg n k) :
    psiv A i (C c) = psi A c := by
  simp [psiv]

lemma psiv_X (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n) (i : Fin n) (l : Fin n) :
    psiv A i (X l) = X (i, l) := by
  simp [psiv]

end RowSpecAux

open RowSpecAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n)
    (B : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n)
    (hAi : ∀ t, A i t = MvPolynomial.C (B i t))
    (hfree : ∀ j t, ∀ v ∈ (A j t).vars, v.1 ≠ i)
    (d : ℕ) (hd : 1 ≤ d) :
    newtonTr (phiPoly (k := k) A res) d =
      ∑ m : Fin (d + 1), (1 / (Nat.factorial (m.val * (k - 1)) : ℚ)) •
        MvPolynomial.aeval
          (fun v : Fin n × Fin n => if v.1 = i then (0 : AuxPoly n) else MvPolynomial.X v)
          ((tfhat (k := k) B i)^[m.val]
            (newtonTr (phiPoly (k := k)
              (Function.update A i (fun t => ∏ s, MvPolynomial.X (i, t s))) res) d)) := by
  classical
  -- the generic ring and the specialisation maps
  have hψX : ∀ j t, psi (k := k) A (X (j, t)) = A j t := psi_X A
  -- images of generic coefficients are free of row `i`
  have hψfree : ∀ c : Rg n k, ∀ v ∈ ((psi (k := k) A) c).vars, v.1 ≠ i := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a =>
      intro v hv
      have hc : psi (k := k) A (C a) = C a := psi_C A a
      rw [hc, vars_C] at hv
      simp at hv
    | add p q hp hq =>
      intro v hv
      rw [map_add] at hv
      rcases Finset.mem_union.mp (vars_add_subset _ _ hv) with h | h
      · exact hp v h
      · exact hq v h
    | mul_X p w hp =>
      intro v hv
      rw [map_mul] at hv
      rcases Finset.mem_union.mp (vars_mul _ _ hv) with h | h
      · exact hp v h
      · rw [hψX] at h; exact hfree w.1 w.2 v h
  -- `(psi (k := k) A) ∘ eval 0 = Z i ∘ (psiv (k := k) A i)`
  have hZ : ∀ p : MvPolynomial (Fin n) (Rg n k), (psi (k := k) A) (eval 0 p) = Z i ((psiv (k := k) A i) p) := by
    intro p
    have : ((psi (k := k) A : Rg n k →ₐ[ℚ] AuxPoly n) : Rg n k →+* AuxPoly n).comp (eval (0 : Fin n → Rg n k)) =
        ((Z i : AuxPoly n →ₐ[ℚ] AuxPoly n) : AuxPoly n →+* AuxPoly n).comp (psiv (k := k) A i) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun l => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, eval_C, psiv_C]
        exact (Z_of_free i (hψfree c)).symm
      · simp [psiv_X, Z]
    exact congrArg (fun f : MvPolynomial (Fin n) (Rg n k) →+* AuxPoly n => f p) this
  -- `(psiv (k := k) A i)` intertwines `∂_{v_l}` with `∂_{(i,l)}`
  have hD : ∀ (l : Fin n) (p : MvPolynomial (Fin n) (Rg n k)),
      (psiv (k := k) A i) (pderiv l p) = pderiv (i, l) ((psiv (k := k) A i) p) := by
    intro l p
    induction p using MvPolynomial.induction_on with
    | C c =>
      simp only [pderiv_C, map_zero, psiv_C]
      exact (pderiv_of_free i l (hψfree c)).symm
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p w hp =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp,
        map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      congr 1
      simp only [psiv_X, pderiv_X]
      by_cases hwl : w = l
      · subst hwl; simp
      · have : (i, w) ≠ (i, l) := fun h => hwl (congrArg Prod.snd h)
        simp [Pi.single_apply, hwl, this]
  have hfold : ∀ (l : List (Fin n)) (p : MvPolynomial (Fin n) (Rg n k)),
      (psiv (k := k) A i) (l.foldr (fun j q => pderiv j q) p) =
        l.foldr (fun j q => pderiv (i, j) q) ((psiv (k := k) A i) p) := by
    intro l p
    induction l with
    | nil => rfl
    | cons j l ih => simp only [List.foldr_cons]; rw [hD, ih]
  have hop : ∀ p : MvPolynomial (Fin n) (Rg n k),
      (psiv (k := k) A i) (∑ t : Fin (k - 1) → Fin n, (X (i, t) : Rg n k) • (List.ofFn t).foldr
          (fun j q => pderiv j q) p) = tfhat (k := k) B i ((psiv (k := k) A i) p) := by
    intro p
    rw [map_sum]
    unfold tfhat
    refine sum_congr rfl fun t _ => ?_
    rw [smul_eq_C_mul, map_mul, hfold]
    simp only [psiv_C, hψX, hAi]
    rw [smul_eq_C_mul]
  have hiter : ∀ (m : ℕ) (p : MvPolynomial (Fin n) (Rg n k)),
      (psiv (k := k) A i) ((fun p : MvPolynomial (Fin n) (Rg n k) => ∑ t : Fin (k - 1) → Fin n, (X (i, t) : Rg n k) •
          (List.ofFn t).foldr (fun j q => pderiv j q) p)^[m] p) =
        (tfhat (k := k) B i)^[m] ((psiv (k := k) A i) p) := by
    intro m
    induction m with
    | zero => intro p; rfl
    | succ m ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hop, ih]
  -- the generic tensors specialise to `A` and to `A` with row `i` replaced
  have hA : (fun j t => ((psi (k := k) A : Rg n k →ₐ[ℚ] AuxPoly n) : Rg n k →+* AuxPoly n) (X (j, t))) = A := by
    funext j t; exact hψX j t
  have hAv : (fun j t => (psiv (k := k) A i) (if j = i then ∏ s, (X (t s) : MvPolynomial (Fin n) (Rg n k))
      else C (X (j, t)))) = Function.update A i (fun t => ∏ s, X (i, t s)) := by
    funext j t
    by_cases hj : j = i
    · subst hj; simp [psiv_X]
    · rw [if_neg hj, Function.update_of_ne hj]
      simp [psiv_C, hψX]
  have hgen := newtonTr_generic_row_invariance n k hk hn res hres i d hd
  have h1 := newtonTr_phiPoly_map ((psi (k := k) A : Rg n k →ₐ[ℚ] AuxPoly n) : Rg n k →+* AuxPoly n)
    (fun j t => (X (j, t) : Rg n k)) res d
  rw [hA] at h1
  rw [h1, hgen, map_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [AlgHom.coe_toRingHom, map_smul, hZ, hiter]
  have h2 := newtonTr_phiPoly_map (psiv (k := k) A i)
    (fun j t => if j = i then ∏ s, (X (t s) : MvPolynomial (Fin n) (Rg n k))
      else C (X (j, t))) res d
  rw [hAv] at h2
  rw [← h2]
  rfl
