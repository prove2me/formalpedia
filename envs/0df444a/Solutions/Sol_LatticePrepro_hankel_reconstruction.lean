-- Prove2me | solution 1 for LatticePrepro.hankel_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:30:42.810947+00:00
-- url     : https://prove2.me/submissions/84c7f466-ef10-4c00-959f-841d0446ea4d

import Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Tables_Hankel
import Theorems.Thm_LatticePrepro_exists_zmod_of_pow_eq

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.Hankel end LatticePrepro.Hankel

namespace LatticePrepro

open Finsupp

section Moment

variable {F Ω : Type*} [CommRing F] [CommRing Ω] [Algebra F Ω]

lemma moment_eq_sum (f : Ω →₀ F) (k : ℕ) :
    moment f k = ∑ α ∈ f.support, f α • α ^ k := rfl

lemma moment_eq_sum_of_subset (f : Ω →₀ F) (k : ℕ) {s : Finset Ω} (hs : f.support ⊆ s) :
    moment f k = ∑ α ∈ s, f α • α ^ k := by
  rw [moment_eq_sum]
  exact Finset.sum_subset hs fun α _ hα => by
    simp [Finsupp.notMem_support_iff.mp hα]

end Moment

end LatticePrepro

namespace LatticePrepro

open Polynomial

namespace Hankel

variable {Ω : Type*} [Field Ω]

/-- The linear functional `f ↦ ∑ i, f_i · y_{j+i}` on polynomials. -/
noncomputable def seqFun (y : ℕ → Ω) (j : ℕ) : Polynomial Ω →ₗ[Ω] Ω where
  toFun f := f.sum fun i a => a * y (j + i)
  map_add' f g :=
    Polynomial.sum_add_index f g _ (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Polynomial.sum_smul_index f c (fun i a => a * y (j + i)) (fun _ => zero_mul _)]
    simp only [Polynomial.sum_def, Finset.mul_sum, mul_assoc]

lemma seqFun_apply (y : ℕ → Ω) (j : ℕ) (f : Polynomial Ω) :
    seqFun y j f = f.sum fun i a => a * y (j + i) := rfl

lemma seqFun_monomial (y : ℕ → Ω) (j n : ℕ) (a : Ω) :
    seqFun y j (monomial n a) = a * y (j + n) := by
  rw [seqFun_apply, Polynomial.sum_monomial_index a (fun i a => a * y (j + i)) (zero_mul _)]

lemma seqFun_C_mul_X_pow (y : ℕ → Ω) (j n : ℕ) (a : Ω) :
    seqFun y j (C a * X ^ n) = a * y (j + n) := by
  rw [C_mul_X_pow_eq_monomial, seqFun_monomial]

lemma seqFun_X_pow (y : ℕ → Ω) (j n : ℕ) : seqFun y j (X ^ n) = y (j + n) := by
  simpa using seqFun_C_mul_X_pow y j n 1

lemma seqFun_C_mul (y : ℕ → Ω) (j : ℕ) (a : Ω) (f : Polynomial Ω) :
    seqFun y j (C a * f) = a * seqFun y j f := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

lemma seqFun_X_pow_mul (y : ℕ → Ω) (j k : ℕ) (f : Polynomial Ω) :
    seqFun y j (X ^ k * f) = seqFun y (j + k) f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial,
      show (X : Polynomial Ω) ^ k * (C a * X ^ n) = C a * X ^ (n + k) by ring,
      seqFun_C_mul_X_pow, seqFun_C_mul_X_pow, show j + (n + k) = j + k + n by omega]

/-- `χ` annihilates the sequence `y` on the first `ℓ` shifts: `∑ i, χ_i y_{j+i} = 0` for `j < ℓ`. -/
def Annihilates (y : ℕ → Ω) (ℓ : ℕ) (χ : Polynomial Ω) : Prop := ∀ j < ℓ, seqFun y j χ = 0

lemma Annihilates.mul_C {y : ℕ → Ω} {ℓ : ℕ} {χ : Polynomial Ω} (h : Annihilates y ℓ χ) (a : Ω) :
    Annihilates y ℓ (χ * C a) := by
  intro j hj
  rw [mul_comm, seqFun_C_mul, h j hj, mul_zero]

/-- If `χ` annihilates `y` on the first `ℓ` shifts, then `seqFun y 0 (g χ) = 0` for `deg g < ℓ`. -/
lemma Annihilates.seqFun_mul_eq_zero {y : ℕ → Ω} {ℓ : ℕ} {χ : Polynomial Ω} (h : Annihilates y ℓ χ)
    {g : Polynomial Ω} (hg : g.natDegree < ℓ) : seqFun y 0 (g * χ) = 0 := by
  conv_lhs => rw [g.as_sum_support_C_mul_X_pow]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [mul_assoc, seqFun_C_mul, seqFun_X_pow_mul, zero_add,
    h i ((le_natDegree_of_mem_supp i hi).trans_lt hg), mul_zero]

/-- The functional `ψ(f) = seqFun y 0 (f %ₘ χ)` of the paper. -/
noncomputable def psi (y : ℕ → Ω) (χ : Polynomial Ω) : Polynomial Ω →ₗ[Ω] Ω :=
  (seqFun y 0) ∘ₗ (modByMonicHom χ)

lemma psi_apply (y : ℕ → Ω) (χ f : Polynomial Ω) : psi y χ f = seqFun y 0 (f %ₘ χ) := rfl

section Psi

variable {y : ℕ → Ω} {ℓ : ℕ} {χ : Polynomial Ω}

lemma psi_eq_zero_of_dvd (hχ : χ.Monic) {f : Polynomial Ω} (hf : χ ∣ f) : psi y χ f = 0 := by
  rw [psi_apply, (modByMonic_eq_zero_iff_dvd hχ).mpr hf, map_zero]

lemma psi_eq_of_dvd_sub (hχ : χ.Monic) {f g : Polynomial Ω} (h : χ ∣ f - g) :
    psi y χ f = psi y χ g := by
  rw [← sub_eq_zero, ← map_sub]
  exact psi_eq_zero_of_dvd hχ h

lemma psi_C_mul (a : Ω) (f : Polynomial Ω) : psi y χ (C a * f) = a * psi y χ f := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-- `ψ` agrees with `seqFun y 0` below degree `ℓ + deg χ`. -/
lemma psi_eq_seqFun (hχ : χ.Monic) (hann : Annihilates y ℓ χ) (hℓ0 : 0 < ℓ) {f : Polynomial Ω}
    (hf : f.natDegree < ℓ + χ.natDegree) : psi y χ f = seqFun y 0 f := by
  conv_rhs => rw [← modByMonic_add_div f χ]
  rw [map_add, psi_apply, mul_comm, hann.seqFun_mul_eq_zero ?_, add_zero]
  rw [natDegree_divByMonic f hχ]
  omega

lemma psi_X_pow (hχ : χ.Monic) (hann : Annihilates y ℓ χ) (hℓ0 : 0 < ℓ) {k : ℕ}
    (hk : k < ℓ + χ.natDegree) : psi y χ (X ^ k) = y k := by
  rw [psi_eq_seqFun hχ hann hℓ0 (by rwa [natDegree_X_pow]), seqFun_X_pow, zero_add]

lemma natDegree_modByMonic_le (hχ : χ.Monic) (f : Polynomial Ω) {N : ℕ} (hN : χ.natDegree ≤ N + 1) :
    (f %ₘ χ).natDegree ≤ N := by
  rcases eq_or_ne (f %ₘ χ) 0 with h0 | h0
  · rw [h0, natDegree_zero]; exact Nat.zero_le _
  · have := natDegree_lt_natDegree h0 (degree_modByMonic_lt f hχ)
    omega

lemma dvd_sub_modByMonic (f : Polynomial Ω) : χ ∣ f - f %ₘ χ := by
  refine ⟨f /ₘ χ, ?_⟩
  exact (eq_sub_of_add_eq (by rw [add_comm]; exact modByMonic_add_div f χ)).symm

end Psi

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] [CharP Ω p]

/-- For a polynomial `b` whose coefficients sit at positions where the Frobenius identities hold,
`seqFun y 0 (b ^ p) = (seqFun y 0 b) ^ p`. -/
lemma seqFun_pow_char {y : ℕ → Ω} {N : ℕ} (hfrob : ∀ k ≤ N, y (p * k) = y k ^ p) {b : Polynomial Ω}
    (hb : b.natDegree ≤ N) : seqFun y 0 (b ^ p) = (seqFun y 0 b) ^ p := by
  have hb' : ∀ i ∈ b.support, y (p * i) = y i ^ p := fun i hi =>
    hfrob i ((le_natDegree_of_mem_supp i hi).trans hb)
  conv_lhs => rw [b.as_sum_support_C_mul_X_pow]
  rw [sum_pow_char, map_sum]
  conv_rhs => rw [seqFun_apply, Polynomial.sum_def, sum_pow_char]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_pow, ← C_pow, ← pow_mul, seqFun_C_mul_X_pow, zero_add, zero_add, mul_comm i p,
    hb' i hi, mul_pow]

variable {y : ℕ → Ω} {ℓ N : ℕ} {χ : Polynomial Ω}
  (hχ : χ.Monic) (hann : Annihilates y ℓ χ) (hfrob : ∀ k ≤ N, y (p * k) = y k ^ p)
  (hN : χ.natDegree ≤ N + 1) (hℓ : p * N < ℓ)
include hχ hann hfrob hN hℓ

/-- `ψ(f ^ p) = ψ(f) ^ p`. -/
lemma psi_pow_char (f : Polynomial Ω) : psi y χ (f ^ p) = (psi y χ f) ^ p := by
  have hbdeg : (f %ₘ χ).natDegree ≤ N := natDegree_modByMonic_le hχ f hN
  have h1 : psi y χ (f ^ p) = psi y χ ((f %ₘ χ) ^ p) :=
    psi_eq_of_dvd_sub hχ ((dvd_sub_modByMonic f).trans (sub_dvd_pow_sub_pow _ _ _))
  rw [h1, psi_eq_seqFun hχ hann (Nat.lt_of_le_of_lt (Nat.zero_le _) hℓ) ?_,
    seqFun_pow_char hfrob hbdeg, psi_apply]
  calc ((f %ₘ χ) ^ p).natDegree ≤ p * (f %ₘ χ).natDegree := natDegree_pow_le
    _ ≤ p * N := Nat.mul_le_mul_left p hbdeg
    _ < ℓ := hℓ
    _ ≤ ℓ + χ.natDegree := Nat.le_add_right _ _

/-- `ψ(f ^ (p ^ e)) = ψ(f) ^ (p ^ e)`. -/
lemma psi_pow_char_pow (f : Polynomial Ω) (e : ℕ) : psi y χ (f ^ p ^ e) = (psi y χ f) ^ p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_mul, psi_pow_char hχ hann hfrob hN hℓ, ih, ← pow_mul, ← pow_succ]

end Frobenius

section Roots

/-- The roots of `nodal s id` are the elements of `s`. -/
lemma roots_nodal_id (s : Finset Ω) : (Lagrange.nodal s id).roots = s.val := by
  rw [Lagrange.nodal_eq]
  exact roots_prod_X_sub_C s

variable [IsAlgClosed Ω] [DecidableEq Ω] {χ : Polynomial Ω}

/-- If `χ` has at most `n` roots counted with multiplicity, then `χ` divides the `n`-th power of
the squarefree polynomial with the same roots. -/
lemma dvd_nodal_pow (hχ : χ ≠ 0) {n : ℕ} (hn : χ.natDegree ≤ n) :
    χ ∣ (Lagrange.nodal χ.roots.toFinset id) ^ n := by
  rw [IsAlgClosed.dvd_iff_roots_le_roots hχ (pow_ne_zero _ Lagrange.nodal_ne_zero), roots_pow,
    roots_nodal_id, Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul, Multiset.toFinset_val, Multiset.count_dedup]
  by_cases ha : a ∈ χ.roots
  · rw [if_pos ha, mul_one]
    calc χ.roots.count a ≤ Multiset.card χ.roots := Multiset.count_le_card _ _
      _ = χ.natDegree := IsAlgClosed.card_roots_eq_natDegree
      _ ≤ n := hn
  · rw [if_neg ha, mul_zero, Multiset.count_eq_zero.mpr ha]

/-- A polynomial with simple roots divides every polynomial vanishing at all its roots. -/
lemma dvd_of_forall_root_eval_eq_zero (hχ0 : χ ≠ 0) (hnd : χ.roots.Nodup) {q : Polynomial Ω}
    (hq : ∀ α ∈ χ.roots.toFinset, q.eval α = 0) : χ ∣ q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · exact dvd_zero _
  rw [IsAlgClosed.dvd_iff_roots_le_roots hχ0 hq0, Multiset.le_iff_subset hnd]
  intro α hα
  rw [mem_roots hq0]
  exact hq α (Multiset.mem_toFinset.mpr hα)

end Roots

end Hankel

open Hankel

/-- **Theorem A.7** (moment reconstruction). -/
private theorem hankel_reconstruction {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω]
    [Algebra (ZMod p) Ω] [IsAlgClosed Ω] {r : ℕ} (hr : 2 ≤ r) (y : ℕ → Ω)
    (hfrob : ∀ k, p * k ≤ 2 * hankelLen p r - 2 → y (p * k) = y k ^ p)
    {t : ℕ} (ht : t < r)
    (hdep : ∃ c : Fin (t + 1) → Ω, c ≠ 0 ∧
      ∀ i : Fin (hankelLen p r), ∑ j, c j * y (i.val + j.val) = 0) :
    ∃ f : Ω →₀ ZMod p, f.support.card ≤ t ∧ ∀ k < hankelLen p r, y k = moment f k := by
  classical
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap (ZMod p) Ω).injective p
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  set ℓ := hankelLen p r with hℓdef
  have hℓ_eq : ℓ = p * (r - 1) + 1 := rfl
  /- Step 0: a nonzero polynomial of degree `≤ t` annihilating `y`, from the dependence. -/
  have hχc : ∃ χ : Polynomial Ω, χ ≠ 0 ∧ χ.natDegree ≤ t ∧ Annihilates y ℓ χ := by
    obtain ⟨c, hc0, hc⟩ := hdep
    set χc : Polynomial Ω := ∑ j : Fin (t + 1), C (c j) * X ^ (j : ℕ) with hχc_def
    have hcoeff : ∀ n : ℕ, χc.coeff n = ∑ j : Fin (t + 1), if n = (j : ℕ) then c j else 0 := by
      intro n
      rw [hχc_def, finsetSum_coeff]
      simp only [coeff_C_mul_X_pow]
    refine ⟨χc, ?_, ?_, ?_⟩
    · intro h0
      apply hc0
      funext j₀
      have h1 := hcoeff j₀
      rw [h0, coeff_zero, Finset.sum_eq_single j₀ (fun j _ hj => if_neg fun h => hj (Fin.ext h.symm))
        (fun h => absurd (Finset.mem_univ _) h), if_pos rfl] at h1
      exact h1.symm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [hcoeff]
      exact Finset.sum_eq_zero fun j _ => if_neg (by have := j.isLt; omega)
    · intro i hi
      rw [hχc_def, map_sum]
      simp only [seqFun_C_mul_X_pow]
      exact hc ⟨i, hi⟩
  /- Step 1: the shortest recurrence. -/
  let P : ℕ → Prop := fun d => ∃ χ : Polynomial Ω, χ ≠ 0 ∧ χ.natDegree = d ∧ Annihilates y ℓ χ
  obtain ⟨χc, hχc0, hχct, hχcann⟩ := hχc
  have hex : ∃ d, P d := ⟨_, χc, hχc0, rfl, hχcann⟩
  have hspec : P (Nat.find hex) := Nat.find_spec hex
  have hmin' : ∀ m, P m → Nat.find hex ≤ m := fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = h at hspec hmin'
  obtain ⟨χ₀, hχ₀0, hχ₀deg, hχ₀ann⟩ := hspec
  have hmin : ∀ χ' : Polynomial Ω, χ' ≠ 0 → Annihilates y ℓ χ' → h ≤ χ'.natDegree :=
    fun χ' h1 h2 => hmin' _ ⟨χ', h1, rfl, h2⟩
  have hht : h ≤ t := (hmin χc hχc0 hχcann).trans hχct
  -- normalize to a monic polynomial
  set χ : Polynomial Ω := χ₀ * C (leadingCoeff χ₀)⁻¹ with hχdef
  have hχ : χ.Monic := monic_mul_leadingCoeff_inv hχ₀0
  have hχdeg : χ.natDegree = h := by
    rw [hχdef, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hχ₀0)), hχ₀deg]
  have hann : Annihilates y ℓ χ := hχ₀ann.mul_C _
  /- Frobenius hypotheses in the form used by `psi_pow_char`. -/
  set N := r - 2 with hN
  have hfrob' : ∀ k ≤ N, y (p * k) = y k ^ p := by
    intro k hk
    apply hfrob
    have h1 : p * k ≤ p * (r - 1) := Nat.mul_le_mul_left p (by omega)
    omega
  have hNdeg : χ.natDegree ≤ N + 1 := by omega
  have hℓN : p * N < ℓ := by
    have h1 : p * N ≤ p * (r - 1) := Nat.mul_le_mul_left p (by omega)
    omega
  /- Step 2: `χ` has distinct roots. -/
  set rs : Finset Ω := χ.roots.toFinset with hrs
  set G : Polynomial Ω := Lagrange.nodal rs id with hG
  have hGdeg : G.natDegree = rs.card := Lagrange.natDegree_nodal
  have hu_le : rs.card ≤ h := by
    calc rs.card ≤ Multiset.card χ.roots := Multiset.toFinset_card_le _
      _ = χ.natDegree := IsAlgClosed.card_roots_eq_natDegree
      _ = h := hχdeg
  -- `ψ (f G) = 0` for every `f`
  have hpsiG : ∀ f : Polynomial Ω, psi y χ (f * G) = 0 := by
    intro f
    have hdvd : χ ∣ (f * G) ^ p ^ h := by
      rw [mul_pow]
      exact dvd_mul_of_dvd_right (dvd_nodal_pow hχ.ne_zero (by rw [hχdeg]; exact (Nat.lt_pow_self hp.out.one_lt).le)) _
    have h1 := psi_eq_zero_of_dvd (y := y) hχ hdvd
    rw [psi_pow_char_pow hχ hann hfrob' hNdeg hℓN] at h1
    exact (pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)).mp h1
  have hℓ0 : 0 < ℓ := Nat.succ_pos _
  have hu_ge : h ≤ rs.card := by
    rw [← hGdeg]
    refine hmin G Lagrange.nodal_ne_zero fun j hj => ?_
    rw [← zero_add j, ← seqFun_X_pow_mul, ← psi_eq_seqFun hχ hann hℓ0 ?_, hpsiG]
    calc (X ^ j * G).natDegree ≤ (X ^ j : Polynomial Ω).natDegree + G.natDegree := natDegree_mul_le
      _ ≤ j + h := by rw [natDegree_X_pow, hGdeg]; omega
      _ < ℓ + χ.natDegree := by omega
  have hnd : χ.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup, IsAlgClosed.card_roots_eq_natDegree, hχdeg]
    exact le_antisymm hu_le hu_ge
  /- Step 3: Lagrange interpolation at the roots. -/
  have hinj : Set.InjOn (id : Ω → Ω) (rs : Set Ω) := Set.injOn_id _
  have hpsi_sum : ∀ g : Polynomial Ω,
      psi y χ g = ∑ α ∈ rs, g.eval α * psi y χ (Lagrange.basis rs id α) := by
    intro g
    have hdvd : χ ∣ g - Lagrange.interpolate rs id (fun α => g.eval α) :=
      dvd_of_forall_root_eval_eq_zero hχ.ne_zero hnd fun α hα => by
        have := Lagrange.eval_interpolate_at_node (r := fun α => g.eval α) hinj hα
        simp only [id_eq] at this
        rw [eval_sub, this, sub_self]
    rw [psi_eq_of_dvd_sub hχ hdvd, Lagrange.interpolate_apply, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [psi_C_mul]
  -- the coefficients are fixed by Frobenius
  have hfix : ∀ α ∈ rs, (psi y χ (Lagrange.basis rs id α)) ^ p = psi y χ (Lagrange.basis rs id α) := by
    intro α hα
    have hdvd : χ ∣ (Lagrange.basis rs id α) ^ p - Lagrange.basis rs id α :=
      dvd_of_forall_root_eval_eq_zero hχ.ne_zero hnd fun β hβ => by
        rw [eval_sub, eval_pow]
        by_cases hβα : β = α
        · subst hβα
          have := Lagrange.eval_basis_self hinj hβ
          simp only [id_eq] at this
          rw [this, one_pow, sub_self]
        · have := Lagrange.eval_basis_of_ne (s := rs) (v := id) (Ne.symm hβα) hβ
          simp only [id_eq] at this
          rw [this, zero_pow hp.out.ne_zero, sub_self]
    rw [← psi_pow_char hχ hann hfrob' hNdeg hℓN]
    exact psi_eq_of_dvd_sub hχ hdvd
  -- choose prime-field coefficients
  have hcoef : ∀ α ∈ rs, ∃ a : ZMod p, algebraMap (ZMod p) Ω a = psi y χ (Lagrange.basis rs id α) :=
    fun α hα => exists_zmod_of_pow_eq (hfix α hα)
  choose! a ha using hcoef
  /- Step 4: the coefficient function. -/
  refine ⟨Finsupp.onFinset rs (fun α => if α ∈ rs then a α else 0) (fun α hα => by
    by_contra h; exact hα (if_neg h)), ?_, ?_⟩
  · exact (Finset.card_le_card Finsupp.support_onFinset_subset).trans (hu_le.trans hht)
  · intro k hk
    rw [moment_eq_sum_of_subset _ k Finsupp.support_onFinset_subset,
      ← psi_X_pow hχ hann hℓ0 (by omega), hpsi_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finsupp.onFinset_apply, if_pos hα, Algebra.smul_def, ha α hα, eval_pow, eval_X, mul_comm]

end LatticePrepro

open LatticePrepro
open Polynomial
theorem solution {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω]
    [Algebra (ZMod p) Ω] [IsAlgClosed Ω] {r : ℕ} (hr : 2 ≤ r) (y : ℕ → Ω)
    (hfrob : ∀ k, p * k ≤ 2 * hankelLen p r - 2 → y (p * k) = y k ^ p)
    {t : ℕ} (ht : t < r)
    (hdep : ∃ c : Fin (t + 1) → Ω, c ≠ 0 ∧
      ∀ i : Fin (hankelLen p r), ∑ j, c j * y (i.val + j.val) = 0) :
    ∃ f : Ω →₀ ZMod p, f.support.card ≤ t ∧ ∀ k < hankelLen p r, y k = moment f k :=
  @LatticePrepro.hankel_reconstruction p _ Ω _ _ _ r hr y hfrob t ht hdep
