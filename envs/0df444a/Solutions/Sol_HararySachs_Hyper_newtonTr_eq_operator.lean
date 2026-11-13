-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_eq_operator
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T21:23:10.817147+00:00
-- url     : https://prove2.me/submissions/48e390e9-df6b-4ae8-a115-847a2f0e2ef9

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Theorems.Thm_HararySachs_Hyper_newtonTr_row_invariance
import Theorems.Thm_HararySachs_Hyper_newtonTr_vTensor_isHomogeneous

open HararySachs.Hyper MvPolynomial Finset

set_option linter.unusedSectionVars false

namespace OpCompAux

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

end Naturality

variable {n : ℕ}

/-! ### Linear-map form of the operators -/

lemma pderiv_comm (a b : Fin n × Fin n) (p : AuxPoly n) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  ext s
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases hab : a = b
  · subst hab; rfl
  · have h1 : (s + Finsupp.single a 1 : (Fin n × Fin n) →₀ ℕ) b = s b := by
      simp [hab]
    have h2 : (s + Finsupp.single b 1 : (Fin n × Fin n) →₀ ℕ) a = s a := by
      simp [Ne.symm hab]
    rw [h1, h2, add_right_comm s]
    ring

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

/-! ### Commutation -/

lemma comm_wordL (i j : Fin n) (l l' : List (Fin n)) : Commute (wordL i l) (wordL j l') := by
  have hd : ∀ (u : Fin n × Fin n) (l' : List (Fin n)),
      Commute ((pderiv u).toLinearMap : Module.End ℚ (AuxPoly n)) (wordL j l') := by
    intro u l'
    induction l' with
    | nil => exact Commute.one_right _
    | cons x l' ih =>
      refine Commute.mul_right ?_ ih
      exact LinearMap.ext fun p => pderiv_comm u (j, x) p
  induction l with
  | nil => exact Commute.one_left _
  | cons x l ih => exact Commute.mul_left (hd _ _) ih

lemma comm_fhL (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i j : Fin n) :
    Commute (fhL A i) (fhL A j) := by
  unfold fhL
  refine Commute.sum_left _ _ _ fun t _ => Commute.sum_right _ _ _ fun t' _ => ?_
  exact ((comm_wordL i j _ _).smul_left _).smul_right _

/-- set the variables of row `i` to zero -/
noncomputable def Z (i : Fin n) : AuxPoly n →ₐ[ℚ] AuxPoly n :=
  aeval (fun v : Fin n × Fin n => if v.1 = i then (0 : AuxPoly n) else X v)

lemma Z_pderiv (i : Fin n) (v : Fin n × Fin n) (hv : v.1 ≠ i) (p : AuxPoly n) :
    Z i (pderiv v p) = pderiv v (Z i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [Z]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p w hp =>
    have hX : Z i (pderiv v (X w)) = pderiv v (Z i (X w)) := by
      simp only [Z, aeval_X, pderiv_X]
      by_cases hwv : w = v
      · subst hwv
        have hw : ¬ w.1 = i := hv
        simp [hw]
      · by_cases hw : w.1 = i
        · simp [hw, Pi.single_apply, hwv]
        · simp [hw, Pi.single_apply, hwv]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp, hX]

lemma comm_Z_fhL (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i j : Fin n) (hij : j ≠ i) :
    Commute ((Z i).toLinearMap : Module.End ℚ (AuxPoly n)) (fhL A j) := by
  have hw : ∀ l : List (Fin n), Commute ((Z i).toLinearMap : Module.End ℚ (AuxPoly n))
      (wordL j l) := by
    intro l
    induction l with
    | nil => exact Commute.one_right _
    | cons x l ih =>
      refine Commute.mul_right ?_ ih
      exact LinearMap.ext fun p => Z_pderiv i (j, x) hij p
  unfold fhL
  exact Commute.sum_right _ _ _ fun t _ => (hw _).smul_right _

lemma comm_Z_applyL {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (a : Fin n → Fin (d + 1))
    (i : Fin n) (hai : (a i).val = 0) :
    Commute ((Z i).toLinearMap : Module.End ℚ (AuxPoly n)) (applyL A a) := by
  have key : ∀ (l : List (Fin n)) (L : Module.End ℚ (AuxPoly n)),
      Commute ((Z i).toLinearMap : Module.End ℚ (AuxPoly n)) L →
      Commute ((Z i).toLinearMap : Module.End ℚ (AuxPoly n))
        (l.foldl (fun L j => fhL A j ^ (a j).val * L) L) := by
    intro l
    induction l with
    | nil => intro L h; exact h
    | cons j l ih =>
      intro L h
      refine ih _ (Commute.mul_right ?_ h)
      by_cases hj : j = i
      · subst hj; rw [hai, pow_zero]; exact Commute.one_right _
      · exact (comm_Z_fhL A i j hj).pow_right _
  exact key _ _ (Commute.one_right _)

lemma coeff_zero_Z (i : Fin n) (p : AuxPoly n) : coeff 0 (Z i p) = coeff 0 p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [Z]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq]
  | mul_X p w hp =>
    rw [map_mul, ← constantCoeff_eq, map_mul, map_mul]
    simp only [Z, aeval_X, constantCoeff_X]
    split_ifs <;> simp

/-- moving `fhL A i ^ c` through a fold of commuting factors -/
lemma foldl_mul_left {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (e : Fin n → Fin (d + 1))
    (C : Module.End ℚ (AuxPoly n)) (hC : ∀ j, Commute C (fhL A j ^ (e j).val)) :
    ∀ (l : List (Fin n)) (L : Module.End ℚ (AuxPoly n)),
      l.foldl (fun L j => fhL A j ^ (e j).val * L) (C * L) =
        C * l.foldl (fun L j => fhL A j ^ (e j).val * L) L := by
  intro l
  induction l with
  | nil => intro L; rfl
  | cons j l ih =>
    intro L
    simp only [List.foldl_cons]
    rw [← ih, ← mul_assoc, ← mul_assoc, (hC j).eq]

lemma applyL_update {d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (a : Fin n → Fin (d + 1))
    (i : Fin n) (hai : (a i).val = 0) (m : Fin (d + 1)) :
    applyL A (Function.update a i m) = fhL A i ^ m.val * applyL A a := by
  classical
  have hcomm : ∀ j, Commute (fhL A i ^ m.val) (fhL A j ^ (a j).val) :=
    fun j => (comm_fhL A i j).pow_pow _ _
  have key : ∀ (l : List (Fin n)) (L : Module.End ℚ (AuxPoly n)),
      l.foldl (fun L j => fhL A j ^ (Function.update a i m j).val * L) L =
        fhL A i ^ (m.val * l.count i) * l.foldl (fun L j => fhL A j ^ (a j).val * L) L := by
    intro l
    induction l with
    | nil => intro L; simp
    | cons j l ih =>
      intro L
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, hai, pow_zero, one_mul, List.count_cons_self,
          foldl_mul_left A a _ hcomm, ← mul_assoc, ← pow_add]
        ring_nf
      · rw [Function.update_of_ne hj, List.count_cons_of_ne hj]
  have hcount : (List.ofFn (fun j : Fin n => j)).count i = 1 :=
    List.count_eq_one_of_mem (List.nodup_ofFn.mpr fun _ _ h => h) (by simp)
  unfold applyL
  rw [key, hcount, mul_one]

/-! ### Degree bookkeeping -/

lemma pderiv_hom (v : Fin n × Fin n) {q : AuxPoly n} {e : ℕ} (hq : q.IsHomogeneous e) :
    (pderiv v q).IsHomogeneous (e - 1) ∧ (e = 0 → pderiv v q = 0) := by
  classical
  have hdeg : ∀ u : (Fin n × Fin n) →₀ ℕ, (Finsupp.weight 1) u = u.degree := fun u => by
    rw [Finsupp.degree_eq_weight_one]; rfl
  have hcoef : ∀ s, coeff s (pderiv v q) ≠ 0 → s.degree + 1 = e := by
    intro s hs
    rw [coeff_pderiv] at hs
    have h1 : coeff (s + Finsupp.single v 1) q ≠ 0 := left_ne_zero_of_mul hs
    have h2 := hq h1
    rw [hdeg, map_add, Finsupp.degree_single] at h2
    exact h2
  refine ⟨fun s hs => ?_, fun he => ?_⟩
  · have := hcoef s hs
    rw [hdeg]
    omega
  · ext s
    rw [coeff_zero]
    by_contra hs
    have := hcoef s hs
    omega

/-- invariant: homogeneous of degree `D - c`, and zero once `c > D` -/
def Hc (D c : ℕ) (q : AuxPoly n) : Prop := q.IsHomogeneous (D - c) ∧ (D < c → q = 0)

lemma Hc_pderiv (D c : ℕ) (v : Fin n × Fin n) {q : AuxPoly n} (h : Hc D c q) :
    Hc D (c + 1) (pderiv v q) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hlt : D < c
  · rw [h2 hlt, map_zero]; exact ⟨isHomogeneous_zero _ _ _, fun _ => rfl⟩
  · obtain ⟨p1, p2⟩ := pderiv_hom v h1
    refine ⟨by rw [show D - (c + 1) = D - c - 1 by omega]; exact p1, fun h => p2 (by omega)⟩

lemma Hc_wordL (D c : ℕ) (i : Fin n) (l : List (Fin n)) {q : AuxPoly n} (h : Hc D c q) :
    Hc D (c + l.length) (wordL i l q) := by
  induction l with
  | nil => simpa [wordL] using h
  | cons j l ih =>
    have := Hc_pderiv D (c + l.length) (i, j) ih
    simpa [wordL, List.length_cons, ← add_assoc] using this

lemma Hc_sum {ι : Type*} (s : Finset ι) (D c : ℕ) (f : ι → AuxPoly n)
    (h : ∀ x ∈ s, Hc D c (f x)) : Hc D c (∑ x ∈ s, f x) :=
  ⟨IsHomogeneous.sum _ _ _ fun x hx => (h x hx).1,
    fun hlt => sum_eq_zero fun x hx => (h x hx).2 hlt⟩

lemma Hc_smul (D c : ℕ) (r : ℚ) {q : AuxPoly n} (h : Hc D c q) : Hc D c (r • q) := by
  refine ⟨?_, fun hlt => by rw [h.2 hlt, smul_zero]⟩
  rw [smul_eq_C_mul]
  simpa using (isHomogeneous_C _ r).mul h.1

lemma Hc_tfhat (D c : ℕ) (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n) {q : AuxPoly n}
    (h : Hc D c q) : Hc D (c + (k - 1)) (tfhat (k := k) A i q) := by
  unfold tfhat
  refine Hc_sum _ _ _ _ fun t _ => Hc_smul _ _ _ ?_
  rw [wordL_apply]
  simpa using Hc_wordL D c i (List.ofFn t) h

lemma Hc_iter (D c : ℕ) (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n) (m : ℕ)
    {q : AuxPoly n} (h : Hc D c q) : Hc D (c + m * (k - 1)) ((tfhat (k := k) A i)^[m] q) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have := Hc_tfhat D _ A i ih
    rwa [add_assoc, ← Nat.succ_mul] at this

lemma Hc_tapplyAll {d : ℕ} (D : ℕ) (A : Fin n → (Fin (k - 1) → Fin n) → ℚ)
    (a : Fin n → Fin (d + 1)) {q : AuxPoly n} (h : Hc D 0 q) :
    Hc D ((∑ j, (a j).val) * (k - 1)) (tapplyAll (k := k) A a q) := by
  have key : ∀ (l : List (Fin n)) (c : ℕ) (q : AuxPoly n), Hc D c q →
      Hc D (c + (l.map fun j => (a j).val).sum * (k - 1))
        (l.foldl (fun q i => ((tfhat (k := k) A i)^[(a i).val]) q) q) := by
    intro l
    induction l with
    | nil => intro c q h; simpa using h
    | cons j l ih =>
      intro c q h
      have := ih _ _ (Hc_iter D c A j (a j).val h)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      have e : c + ((a j).val + (l.map fun j => (a j).val).sum) * (k - 1) =
          c + (a j).val * (k - 1) + (l.map fun j => (a j).val).sum * (k - 1) := by ring
      rw [e]; exact this
  have := key (List.ofFn fun i : Fin n => i) 0 q h
  simpa [tapplyAll, List.sum_ofFn] using this

lemma coeff_zero_tapplyAll_eq_zero {d : ℕ} (hr : 1 ≤ k - 1)
    (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (a : Fin n → Fin (d + 1)) {q : AuxPoly n}
    (hq : q.IsHomogeneous (d * (k - 1))) (ha : (∑ j, (a j).val) ≠ d) :
    coeff 0 (tapplyAll (k := k) A a q) = 0 := by
  have h := Hc_tapplyAll (d * (k - 1)) A a (q := q) ⟨by simpa using hq, fun h => absurd h (by omega)⟩
  by_cases hlt : d * (k - 1) < (∑ j, (a j).val) * (k - 1)
  · rw [h.2 hlt, coeff_zero]
  · apply h.1.coeff_eq_zero
    have hne : (∑ j, (a j).val) * (k - 1) ≠ d * (k - 1) := fun e =>
      ha (Nat.eq_of_mul_eq_mul_right (by omega) e)
    rw [map_zero]
    omega

/-! ### Row-by-row replacement -/

/-- rows `< s` replaced by the power rows of `V`, the others constant -/
noncomputable def Ψ (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (s : ℕ) :
    Fin n → (Fin (k - 1) → Fin n) → AuxPoly n :=
  fun j t => if j.val < s then ∏ x, X (j, t x) else C (A j t)

end OpCompAux

open OpCompAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (d : ℕ) (hd : 1 ≤ d) :
    newtonTr (phiPoly (k := k) A res) d =
      ∑ a : Fin n → Fin (d + 1),
        if (∑ i, (a i).val) = d then
          MvPolynomial.coeff 0
              (tapplyAll (k := k) A a (newtonTr (phiPoly (k := k) (vTensor n k) res) d)) /
            ∏ i, (Nat.factorial ((a i).val * (k - 1)) : ℚ)
        else 0 := by
  classical
  set w : (Fin n → Fin (d + 1)) → ℚ :=
    fun a => 1 / ∏ j, (Nat.factorial ((a j).val * (k - 1)) : ℚ) with hw
  set S : ℕ → Finset (Fin n → Fin (d + 1)) :=
    fun s => univ.filter (fun a => ∀ j : Fin n, s ≤ j.val → (a j).val = 0) with hS
  -- the claim after replacing the first `s` rows
  have claim : ∀ s ≤ n, newtonTr (phiPoly (k := k) A res) d =
      ∑ a ∈ S s, w a * coeff 0 (applyL A a (newtonTr (phiPoly (k := k) (Ψ A s) res) d)) := by
    intro s
    induction s with
    | zero =>
      intro _
      have hS0 : S 0 = {fun _ => 0} := by
        ext a
        simp only [hS, mem_filter, mem_univ, true_and, zero_le, forall_const, mem_singleton]
        refine ⟨fun h => funext fun j => Fin.ext (h j), fun h j => by rw [h]; rfl⟩
      have hΨ : Ψ A 0 = fun j t => (C : ℚ →+* AuxPoly n) (A j t) := by
        funext j t; simp [Ψ]
      have happ : applyL A (fun _ : Fin n => (0 : Fin (d + 1))) = 1 := by
        have : ∀ (l : List (Fin n)) (L : Module.End ℚ (AuxPoly n)),
            l.foldl (fun L j => fhL A j ^ ((fun _ : Fin n => (0 : Fin (d + 1))) j).val * L) L =
              L := by
          intro l
          induction l with
          | nil => intro L; rfl
          | cons j l ih => intro L; simp only [List.foldl_cons]; rw [ih]; simp
        exact this _ _
      rw [hS0, sum_singleton, happ, hΨ, phiPoly_map, newtonTr_map]
      simp [hw]
    | succ s ih =>
      intro hs
      have hs' : s < n := hs
      set i : Fin n := ⟨s, hs'⟩ with hi
      rw [ih (by omega)]
      -- one more row via the single-row invariance
      have hupd : Function.update (Ψ A s) i (fun t => ∏ x, X (i, t x)) = Ψ A (s + 1) := by
        funext j t
        by_cases hj : j = i
        · rw [hj]
          simp only [Function.update_self, Ψ]
          rw [if_pos (by rw [hi]; exact Nat.lt_succ_self s)]
        · rw [Function.update_of_ne hj]
          have : j.val ≠ s := fun h => hj (Fin.ext h)
          simp only [Ψ]
          congr 1
          exact propext ⟨fun h => by omega, fun h => by omega⟩
      have hAi : ∀ t, Ψ A s i t = C (A i t) := by
        intro t
        have hni : ¬ (i.val < s) := by rw [hi]; exact lt_irrefl s
        simp only [Ψ, if_neg hni]
      have hfree : ∀ j t, ∀ v ∈ (Ψ A s j t).vars, v.1 ≠ i := by
        intro j t v hv
        simp only [Ψ] at hv
        split_ifs at hv with hj
        · have := vars_prod (s := univ) (fun x => (X (j, t x) : AuxPoly n)) hv
          rw [mem_biUnion] at this
          obtain ⟨x, _, hx⟩ := this
          rw [vars_X, mem_singleton] at hx
          rw [hx]
          intro h
          have hji : j = i := h
          have : j.val = s := by rw [hji, hi]
          omega
        · rw [vars_C] at hv; simp at hv
      have hrow := newtonTr_row_invariance n k hk hn res hres (Ψ A s) A i hAi hfree d hd
      rw [hupd] at hrow
      set q := newtonTr (phiPoly (k := k) (Ψ A (s + 1)) res) d with hq
      -- expand each term
      have hterm : ∀ a ∈ S s, w a * coeff 0 (applyL A a (newtonTr (phiPoly (k := k) (Ψ A s) res) d)) =
          ∑ m : Fin (d + 1), w (Function.update a i m) *
            coeff 0 (applyL A (Function.update a i m) q) := by
        intro a ha
        have hai : (a i).val = 0 := (mem_filter.mp ha).2 i (by simp [hi])
        rw [hrow, map_sum, coeff_sum, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [map_smul, coeff_smul, iterate_eq]
        rw [show (aeval fun v : Fin n × Fin n => if v.1 = i then (0 : AuxPoly n) else X v) = Z i
          from rfl]
        have h1 : applyL A a (Z i ((fhL A i ^ m.val) q)) =
            Z i (applyL A a ((fhL A i ^ m.val) q)) := by
          have := (comm_Z_applyL A a i hai).eq
          exact (congrArg (fun L : Module.End ℚ (AuxPoly n) => L ((fhL A i ^ m.val) q)) this).symm
        have h2 : applyL A a ((fhL A i ^ m.val) q) = applyL A (Function.update a i m) q := by
          rw [applyL_update A a i hai m]
          have hc : Commute (fhL A i ^ m.val) (applyL A a) := by
            have key : ∀ (l : List (Fin n)) (L : Module.End ℚ (AuxPoly n)),
                Commute (fhL A i ^ m.val) L →
                Commute (fhL A i ^ m.val) (l.foldl (fun L j => fhL A j ^ (a j).val * L) L) := by
              intro l
              induction l with
              | nil => intro L h; exact h
              | cons j l ih' =>
                intro L h
                exact ih' _ (Commute.mul_right ((comm_fhL A i j).pow_pow _ _) h)
            exact key _ _ (Commute.one_right _)
          rw [hc.eq]; rfl
        rw [h1, coeff_zero_Z, h2, smul_eq_mul]
        -- weights
        have hwu : w (Function.update a i m) =
            (1 / (Nat.factorial (m.val * (k - 1)) : ℚ)) * w a := by
          simp only [hw]
          have hp : ∏ j, (Nat.factorial ((Function.update a i m j).val * (k - 1)) : ℚ) =
              (Nat.factorial (m.val * (k - 1)) : ℚ) *
                ∏ j, (Nat.factorial ((a j).val * (k - 1)) : ℚ) := by
            rw [← mul_prod_erase univ _ (mem_univ i), ← mul_prod_erase univ
              (fun j => (Nat.factorial ((a j).val * (k - 1)) : ℚ)) (mem_univ i)]
            rw [Function.update_self, hai, zero_mul, Nat.factorial_zero, Nat.cast_one, one_mul]
            congr 1
            refine prod_congr rfl fun j hj => ?_
            rw [Function.update_of_ne (ne_of_mem_erase hj)]
          rw [hp]
          field_simp
        rw [hwu]; ring
      rw [sum_congr rfl hterm, ← sum_product']
      refine sum_nbij' (fun p => Function.update p.1 i p.2)
        (fun a => (Function.update a i 0, a i)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [mem_product, hS, mem_filter, mem_univ, true_and] at hp ⊢
        intro j hj
        have hji : j ≠ i := fun h => by rw [h] at hj; simp [hi] at hj
        rw [Function.update_of_ne hji]
        exact hp.1 j (by omega)
      · intro a ha
        simp only [mem_product, hS, mem_filter, mem_univ, true_and, and_true] at ha ⊢
        intro j hj
        by_cases hji : j = i
        · rw [hji, Function.update_self]; rfl
        · rw [Function.update_of_ne hji]
          have : j.val ≠ s := fun h => hji (Fin.ext h)
          exact ha j (by omega)
      · intro p hp
        simp only [mem_product, hS, mem_filter, mem_univ, true_and] at hp
        have hpi : p.1 i = 0 := Fin.ext (hp.1 i (by simp [hi]))
        simp only [Function.update_idem, Function.update_self]
        rw [← hpi, Function.update_eq_self]
      · intro a _
        simp
      · intro p _; rfl
  -- all rows replaced
  have hΨn : Ψ A n = vTensor n k := by
    funext j t; simp [Ψ, vTensor, j.isLt]
  have hSn : S n = univ := by
    ext a; simp only [hS, mem_filter, mem_univ, true_and, iff_true]
    intro j hj; exact absurd j.isLt (by omega)
  rw [claim n le_rfl, hΨn, hSn]
  refine sum_congr rfl fun a _ => ?_
  rw [← tapplyAll_eq]
  split_ifs with ha
  · rw [hw]; ring
  · rw [coeff_zero_tapplyAll_eq_zero (by omega) A a
      (newtonTr_vTensor_isHomogeneous n k res d) ha, mul_zero]
