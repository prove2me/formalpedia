-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T18:08:32.910024+00:00
-- url     : https://prove2.me/submissions/2f98d7ef-5e0b-4975-a20d-beaf87e67780

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace Aux_OAI_PiExponent_FormalInterpolation_logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity

/-! ### The logarithmic frame as derivations -/

noncomputable def Dd {m : ℕ} (i : Fin (m + 1)) :
    Derivation ℂ (MvPolynomial (Fin (m + 1)) ℂ) (MvPolynomial (Fin (m + 1)) ℂ) :=
  Fin.cases (motive := fun _ =>
      Derivation ℂ (MvPolynomial (Fin (m + 1)) ℂ) (MvPolynomial (Fin (m + 1)) ℂ))
    ((MvPolynomial.X 0 : MvPolynomial (Fin (m + 1)) ℂ) • MvPolynomial.pderiv 0 +
      ∑ j : Fin m, MvPolynomial.pderiv j.succ)
    (fun j => MvPolynomial.pderiv j.succ) i

lemma Dd_eq {m : ℕ} (i : Fin (m + 1)) (F : MvPolynomial (Fin (m + 1)) ℂ) :
    logarithmicFrameDerivative i F = Dd i F := by
  cases i using Fin.cases with
  | zero =>
    have h : ∀ G : MvPolynomial (Fin (m + 1)) ℂ,
        (∑ j : Fin m, (MvPolynomial.pderiv j.succ :
          Derivation ℂ (MvPolynomial (Fin (m + 1)) ℂ) (MvPolynomial (Fin (m + 1)) ℂ))) G =
        ∑ j : Fin m, MvPolynomial.pderiv j.succ G := by
      intro G
      rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
      rfl
    simp [logarithmicFrameDerivative, Dd, h]
  | succ j => simp [logarithmicFrameDerivative, Dd]

section words

variable {m : ℕ}

lemma lfw_cons (i : Fin (m + 1)) (u : List (Fin (m + 1))) (F : MvPolynomial (Fin (m + 1)) ℂ) :
    logarithmicFrameWord (i :: u) F = Dd i (logarithmicFrameWord u F) := by
  simp [logarithmicFrameWord, Dd_eq]

lemma lfw_append (u u' : List (Fin (m + 1))) (F : MvPolynomial (Fin (m + 1)) ℂ) :
    logarithmicFrameWord (u ++ u') F = logarithmicFrameWord u (logarithmicFrameWord u' F) := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [List.cons_append, lfw_cons, lfw_cons, ih]

/-- Leibniz rule for frame words, in ideal form. -/
lemma lfw_mul_mem (u : List (Fin (m + 1))) (g f : MvPolynomial (Fin (m + 1)) ℂ) :
    logarithmicFrameWord u (g * f) ∈
      Ideal.span {y | ∃ u', u'.Sublist u ∧ y = logarithmicFrameWord u' f} := by
  induction u with
  | nil => exact Ideal.mul_mem_left _ g (Ideal.subset_span ⟨[], List.Sublist.slnil, rfl⟩)
  | cons i u ih =>
    have key : ∀ z ∈ Ideal.span {y | ∃ u', u'.Sublist u ∧ y = logarithmicFrameWord u' f},
        Dd i z ∈ Ideal.span {y | ∃ u', u'.Sublist (i :: u) ∧ y = logarithmicFrameWord u' f} ∧
        z ∈ Ideal.span {y | ∃ u', u'.Sublist (i :: u) ∧ y = logarithmicFrameWord u' f} := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨u', hu', rfl⟩ := hy
        exact ⟨Ideal.subset_span ⟨i :: u', hu'.cons_cons i, (lfw_cons i u' f).symm⟩,
          Ideal.subset_span ⟨u', hu'.cons i, rfl⟩⟩
      | zero => simp
      | add x y _ _ hx hy =>
        exact ⟨by rw [map_add]; exact Ideal.add_mem _ hx.1 hy.1, Ideal.add_mem _ hx.2 hy.2⟩
      | smul r x _ hx =>
        refine ⟨?_, Ideal.mul_mem_left _ r hx.2⟩
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx.1) (Ideal.mul_mem_right _ _ hx.2)
    rw [lfw_cons]
    exact (key _ ih).1

lemma cost_sublist (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < (v i : ℝ))
    {u' u : List (Fin (m + 1))} (h : u'.Sublist u) :
    logarithmicFrameCost v u' ≤ logarithmicFrameCost v u := by
  unfold logarithmicFrameCost
  exact (h.map _).sum_le_sum (by
    intro a ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    exact (hv b).le)

end words

section powers

variable {m : ℕ}

lemma Dd_pow_mem (P : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) (i : Fin (m + 1)) :
    ∀ n, ∀ x ∈ P ^ (n + 1), Dd i x ∈ P ^ n := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      apply Ideal.add_mem
      · rw [pow_succ']
        exact Ideal.mul_mem_mul ha (ih b hb)
      · exact Ideal.mul_mem_right _ _ hb
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

variable (B : Finset (Fin (m + 1)))

/-- Apply frame derivatives with letters of `B`, head letter innermost. -/
noncomputable def Ew : List B → MvPolynomial (Fin (m + 1)) ℂ → MvPolynomial (Fin (m + 1)) ℂ
  | [], x => x
  | j :: w, x => Ew w (Dd (j : Fin (m + 1)) x)

lemma Ew_add (w : List B) (x y : MvPolynomial (Fin (m + 1)) ℂ) :
    Ew B w (x + y) = Ew B w x + Ew B w y := by
  induction w generalizing x y with
  | nil => rfl
  | cons j w ih => simp only [Ew, map_add, ih]

lemma Ew_zero (w : List B) : Ew B w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih => simp only [Ew, map_zero, ih]

lemma Ew_pow (P : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) (w : List B) :
    ∀ n, ∀ x ∈ P ^ (n + w.length), Ew B w x ∈ P ^ n := by
  induction w with
  | nil => intro n x hx; show x ∈ _; simpa using hx
  | cons j w ih =>
    intro n x hx
    apply ih n
    apply Dd_pow_mem P j
    simpa [List.length_cons, add_assoc] using hx

lemma Ew_eq (w : List B) (x : MvPolynomial (Fin (m + 1)) ℂ) :
    Ew B w x = logarithmicFrameWord (w.map Subtype.val).reverse x := by
  induction w generalizing x with
  | nil => rfl
  | cons j w ih =>
    simp only [Ew, ih, List.map_cons, List.reverse_cons, lfw_append]
    rw [lfw_cons]
    rfl

end powers

section claim

variable {m : ℕ} {B : Finset (Fin (m + 1))}
variable (P : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) (F : B → MvPolynomial (Fin (m + 1)) ℂ)
  (δ : MvPolynomial (Fin (m + 1)) ℂ)

noncomputable def G (M : Multiset B) : MvPolynomial (Fin (m + 1)) ℂ := (M.map F).prod

variable {P F δ}

lemma G_cons (k : B) (M : Multiset B) : G F (k ::ₘ M) = F k * G F M := by
  simp [G]

lemma G_mem (hF : ∀ k, F k ∈ P) (M : Multiset B) : G F M ∈ P ^ Multiset.card M := by
  induction M using Multiset.induction_on with
  | empty => simp [G]
  | cons k M ih =>
    rw [G_cons, Multiset.card_cons, pow_succ']
    exact Ideal.mul_mem_mul (hF k) ih

lemma Lj [DecidableEq B] (hF : ∀ k, F k ∈ P)
    (hD : ∀ j k : B, Dd (j : Fin (m + 1)) (F k) - (if j = k then δ else 0) ∈ P)
    (M : Multiset B) (j : B) :
    Dd (j : Fin (m + 1)) (G F M) - (M.count j : MvPolynomial (Fin (m + 1)) ℂ) * δ *
      G F (M.erase j) ∈ P ^ Multiset.card M := by
  induction M using Multiset.induction_on with
  | empty => simp [G]
  | cons k M ih =>
    set r := Dd (j : Fin (m + 1)) (G F M) - (M.count j : MvPolynomial (Fin (m + 1)) ℂ) * δ *
      G F (M.erase j) with hr
    set p := Dd (j : Fin (m + 1)) (F k) - (if j = k then δ else 0) with hp
    have hmem : F k * r + G F M * p ∈ P ^ Multiset.card (k ::ₘ M) := by
      rw [Multiset.card_cons, pow_succ']
      apply Ideal.add_mem
      · exact Ideal.mul_mem_mul (hF k) ih
      · rw [mul_comm (G F M) p]
        exact Ideal.mul_mem_mul (hD j k) (G_mem hF M)
    convert hmem using 1
    rw [G_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hr, hp]
    by_cases hjk : j = k
    · subst hjk
      rw [Multiset.erase_cons_head, Multiset.count_cons_self, if_pos rfl]
      by_cases hjM : j ∈ M
      · have e : G F M = F j * G F (M.erase j) := by
          rw [← G_cons, Multiset.cons_erase hjM]
        push_cast
        rw [e]
        ring
      · have hc : M.count j = 0 := Multiset.count_eq_zero.mpr hjM
        rw [hc]
        push_cast
        ring
    · rw [Multiset.erase_cons_tail M (Ne.symm hjk), Multiset.count_cons_of_ne hjk, if_neg hjk,
        G_cons]
      ring

/-- The main triangularity computation. -/
lemma claim [DecidableEq B] (hF : ∀ k, F k ∈ P)
    (hD : ∀ j k : B, Dd (j : Fin (m + 1)) (F k) - (if j = k then δ else 0) ∈ P) :
    ∀ (w : List B) (M : Multiset B), Multiset.card M = w.length →
      ∀ h : MvPolynomial (Fin (m + 1)) ℂ, ∃ c : ℕ, ((w : Multiset B) = M ↔ c ≠ 0) ∧
        Ew B w (h * G F M) - (c : MvPolynomial (Fin (m + 1)) ℂ) * δ ^ w.length * h ∈ P := by
  intro w
  induction w with
  | nil =>
    intro M hM h
    have hM0 : M = 0 := Multiset.card_eq_zero.mp (by simpa using hM)
    subst hM0
    refine ⟨1, by simp, ?_⟩
    simp [Ew, G]
  | cons j w ih =>
    intro M hM h
    set r := Dd (j : Fin (m + 1)) (G F M) - (M.count j : MvPolynomial (Fin (m + 1)) ℂ) * δ *
      G F (M.erase j) with hr
    have hrmem := Lj hF hD M j
    rw [← hr] at hrmem
    have hrest : Ew B w (h * r + G F M * Dd (j : Fin (m + 1)) h) ∈ P := by
      have h1 : h * r + G F M * Dd (j : Fin (m + 1)) h ∈ P ^ (1 + w.length) := by
        rw [show 1 + w.length = Multiset.card M by rw [hM]; simp [add_comm]]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hrmem)
          (Ideal.mul_mem_right _ _ (G_mem hF M))
      simpa using Ew_pow B P w 1 _ h1
    have hsplit : Ew B (j :: w) (h * G F M) =
        Ew B w (h * ((M.count j : MvPolynomial (Fin (m + 1)) ℂ) * δ) * G F (M.erase j)) +
        Ew B w (h * r + G F M * Dd (j : Fin (m + 1)) h) := by
      rw [← Ew_add]
      simp only [Ew]
      congr 1
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hr]
      ring
    by_cases hjM : j ∈ M
    · have hcard : Multiset.card (M.erase j) = w.length := by
        rw [Multiset.card_erase_of_mem hjM, hM]
        simp
      obtain ⟨c0, hc0iff, hc0⟩ := ih (M.erase j) hcard
        (h * ((M.count j : MvPolynomial (Fin (m + 1)) ℂ) * δ))
      refine ⟨M.count j * c0, ?_, ?_⟩
      · have hcnt : M.count j ≠ 0 := Multiset.count_ne_zero.mpr hjM
        rw [Nat.mul_ne_zero_iff, ← hc0iff]
        simp only [hcnt, ne_eq, not_false_eq_true, true_and]
        rw [← Multiset.cons_coe]
        constructor
        · intro e
          rw [← e, Multiset.erase_cons_head]
        · intro e
          rw [e, Multiset.cons_erase hjM]
      · rw [hsplit]
        have := Ideal.add_mem _ hc0 hrest
        convert this using 1
        push_cast
        simp only [List.length_cons]
        ring
    · have hc : M.count j = 0 := Multiset.count_eq_zero.mpr hjM
      refine ⟨0, ?_, ?_⟩
      · simp only [ne_eq, not_true_eq_false, iff_false]
        intro e
        apply hjM
        rw [← e]
        simp
      · rw [hsplit, hc]
        simpa [Ew_zero] using hrest

end claim

/-! ### Choosing equations with an invertible frame matrix -/

lemma exists_det_ne_zero {ι X K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (v : ι → X → K) (hv : LinearIndependent K v) :
    ∃ F : ι → X, (Matrix.of fun i k => v i (F k)).det ≠ 0 := by
  classical
  let u : X → (ι → K) := fun x i => v i x
  have hspan : Submodule.span K (Set.range u) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hfu : ∀ x, f (u x) = 0 := fun x =>
      LinearMap.mem_ker.mp (hle (Submodule.subset_span ⟨x, rfl⟩))
    let g : ι → K := fun i => f (Pi.single i 1)
    have hf_apply : ∀ y : ι → K, f y = ∑ i, y i * g i := by
      intro y
      conv_lhs => rw [← Finset.univ_sum_single y]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (Pi.single i (y i) : ι → K) = y i • Pi.single i 1 by
        rw [← Pi.single_smul]; simp]
      rw [map_smul, smul_eq_mul]
    have hsum : ∑ i, g i • v i = 0 := by
      funext x
      have := hfu x
      rw [hf_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [u, mul_comm]
    have hg := Fintype.linearIndependent_iff.mp hv g hsum
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [hf_apply]
    simp [hg]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range u)
  rw [hspan] at hbspan
  let basis := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  let e : ι ≃ b := (Pi.basisFun K ι).indexEquiv basis
  have hmem : ∀ k, ∃ x, u x = (e k : ι → K) := fun k => hbsub (e k).2
  choose F hF using hmem
  refine ⟨F, ?_⟩
  have hli : LinearIndependent K (Matrix.of fun i k => v i (F k)).col := by
    have : (Matrix.of fun i k => v i (F k)).col = fun k => ((e k : b) : ι → K) := by
      funext k i
      rw [← hF k]
      rfl
    rw [this]
    exact hbli.comp e e.injective
  have hu := (Matrix.linearIndependent_cols_iff_isUnit (A := Matrix.of fun i k => v i (F k))).mp hli
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero


/-! ### Exponent vectors as multisets -/

section multisets

variable {m : ℕ} {B : Finset (Fin (m + 1))}

noncomputable def Mb (a : B → ℕ) : Multiset B := ∑ k : B, Multiset.replicate (a k) k

lemma Mb_count [DecidableEq B] (a : B → ℕ) (j : B) : (Mb a).count j = a j := by
  simp [Mb, Multiset.count_sum', Multiset.count_replicate]

lemma Mb_card (a : B → ℕ) : Multiset.card (Mb a) = ∑ k, a k := by
  simp [Mb]

lemma Mb_cost (v : Fin (m + 1) → ℚ) (a : B → ℕ) :
    logarithmicFrameCost v (((Mb a).toList.map Subtype.val).reverse) =
      ∑ k : B, (v k : ℝ) * (a k : ℝ) := by
  unfold logarithmicFrameCost
  rw [List.map_reverse, List.sum_reverse, List.map_map]
  have : ((Mb a).toList.map ((fun i => (v i : ℝ)) ∘ Subtype.val)).sum =
      ((Mb a).map (fun k : B => (v k : ℝ))).sum := by
    conv_rhs => rw [← Multiset.coe_toList (Mb a)]
    rw [Multiset.map_coe, Multiset.sum_coe]
    rfl
  rw [this, Mb]
  have gen : ∀ s : Finset B, ((∑ k ∈ s, Multiset.replicate (a k) k).map
      (fun k : B => (v k : ℝ))).sum = ∑ k ∈ s, (v k : ℝ) * (a k : ℝ) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
      ring
  exact gen Finset.univ

end multisets


/-! ### Assembly -/

theorem main {m : Nat} (v : Fin (m + 1) → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (B : Finset (Fin (m + 1)))
    (hB : LinearIndependent (logarithmicPrimeField P)
      (fun i : B => logarithmicNormalColumnAtPrime P i))
    (hwords : ∀ f ∈ S, ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word < T → logarithmicFrameWord word f ∈ P) :
    (strictWeightedSimplexCard (fun i : B => v i) T : ENat) ≤
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P := by
  classical
  -- Step 1: equations whose frame matrix is invertible at the generic point.
  obtain ⟨Fp, hdet⟩ := exists_det_ne_zero _ hB
  let N : Matrix B B (MvPolynomial (Fin (m + 1)) ℂ) :=
    Matrix.of fun i k => Dd (i : Fin (m + 1)) (Fp k : MvPolynomial (Fin (m + 1)) ℂ)
  let δ := N.det
  have hπN : (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P)).mapMatrix N =
      Matrix.of fun (i k : B) => logarithmicNormalColumnAtPrime P (i : Fin (m + 1)) (Fp k) := by
    ext i k
    simp [N, logarithmicNormalColumnAtPrime, Dd_eq]
  have hδ : δ ∉ P := by
    intro hmem
    apply hdet
    rw [← hπN, ← RingHom.map_det]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (m + 1)) ℂ)
      (MvPolynomial (Fin (m + 1)) ℂ ⧸ P) (logarithmicPrimeField P)]
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  let F' : B → MvPolynomial (Fin (m + 1)) ℂ := fun k =>
    ∑ l, (Fp l : MvPolynomial (Fin (m + 1)) ℂ) * N.adjugate l k
  have hF' : ∀ k, F' k ∈ P := fun k =>
    Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_right _ _ (Fp l).2)
  have hD' : ∀ j k : B, Dd (j : Fin (m + 1)) (F' k) - (if j = k then δ else 0) ∈ P := by
    intro j k
    have e : Dd (j : Fin (m + 1)) (F' k) =
        ∑ l, (Fp l : MvPolynomial (Fin (m + 1)) ℂ) * Dd (j : Fin (m + 1)) (N.adjugate l k) +
          (N * N.adjugate) j k := by
      have h1 : Dd (j : Fin (m + 1)) (F' k) = ∑ l, Dd (j : Fin (m + 1))
          ((Fp l : MvPolynomial (Fin (m + 1)) ℂ) * N.adjugate l k) := map_sum _ _ _
      rw [h1, Matrix.mul_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      simp only [N, Matrix.of_apply]
      ring
    rw [e, Matrix.mul_adjugate]
    have : (δ • (1 : Matrix B B (MvPolynomial (Fin (m + 1)) ℂ))) j k = if j = k then δ else 0 := by
      simp [Matrix.one_apply]
    rw [this, add_sub_cancel_right]
    exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_right _ _ (Fp l).2)
  -- Step 2: the simplex, listed by nonincreasing degree.
  let Sx := {a : B → ℕ // ∑ i, ((fun i : B => v i) i : ℝ) * (a i : ℝ) < T}
  have hfin : Finite Sx := by
    let bnd : B → ℕ := fun i => ⌈T / (v i : ℝ)⌉₊
    refine Finite.of_injective (β := ∀ i : B, Fin (bnd i + 1)) (fun a i => ⟨a.1 i, ?_⟩) ?_
    · have hle : (v i : ℝ) * (a.1 i : ℝ) ≤ ∑ j, ((fun i : B => v i) j : ℝ) * (a.1 j : ℝ) :=
        Finset.single_le_sum (f := fun j : B => ((v j : ℝ)) * (a.1 j : ℝ))
          (fun j _ => mul_nonneg (hv j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
      have hlt : (a.1 i : ℝ) < T / (v i : ℝ) := by
        rw [lt_div_iff₀ (hv i)]
        linarith [a.2]
      have : a.1 i ≤ bnd i := by
        have := le_trans hlt.le (Nat.le_ceil _)
        exact_mod_cast this
      omega
    · intro a b h
      apply Subtype.ext
      funext i
      have := congrFun h i
      simpa using congrArg Fin.val this
  let _ : Fintype Sx := Fintype.ofFinite Sx
  let deg : Sx → ℕ := fun a => ∑ k, a.1 k
  let L : List Sx := (Finset.univ : Finset Sx).toList.mergeSort (fun a b => decide (deg b ≤ deg a))
  have hLlen : L.length = Nat.card Sx := by
    simp [L, Nat.card_eq_fintype_card]
  have hLnodup : L.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  have hLsorted : L.Pairwise (fun a b => decide (deg b ≤ deg a) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc
      simp only [decide_eq_true_eq] at *
      omega
    · intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
  -- Step 3: the ideals.
  let J : Ideal (MvPolynomial (Fin (m + 1)) ℂ) := Ideal.span (↑S : Set _)
  let wd : Sx → List B := fun a => (Mb a.1).toList
  have wd_len : ∀ a, (wd a).length = deg a := fun a => by
    simp [wd, Mb_card, deg]
  have wd_coe : ∀ a, ((wd a : List B) : Multiset B) = Mb a.1 := fun a => Multiset.coe_toList _
  let Q : List B → Ideal (MvPolynomial (Fin (m + 1)) ℂ) := fun w =>
    { carrier := {x | ∀ h, Ew B w (h * x) ∈ P}
      add_mem' := by
        intro x y hx hy h
        simp only [Set.mem_ofPred_eq] at *
        rw [mul_add, Ew_add]
        exact Ideal.add_mem _ (hx h) (hy h)
      zero_mem' := by
        intro h
        simp [Ew_zero]
      smul_mem' := by
        intro c x hx h
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
        rw [← mul_assoc]
        exact hx (h * c) }
  let W : ℕ → Ideal (MvPolynomial (Fin (m + 1)) ℂ) := fun i =>
    J ⊔ Ideal.span {y | ∃ j : Fin L.length, j.val < i ∧ y = G F' (Mb (L.get j).1)}
  have Mb_inj : ∀ a b : Sx, Mb a.1 = Mb b.1 → a = b := by
    intro a b h
    apply Subtype.ext
    funext k
    rw [← Mb_count a.1 k, ← Mb_count b.1 k, h]
  have key : ∀ i (hi : i < L.length), W i ≤ Q (wd (L.get ⟨i, hi⟩)) := by
    intro i hi
    set a := L.get ⟨i, hi⟩ with ha
    apply sup_le
    · rw [Ideal.span_le]
      intro f hf h
      show Ew B (wd a) (h * f) ∈ P
      rw [Ew_eq]
      have hc : logarithmicFrameCost v (((wd a).map Subtype.val).reverse) < T := by
        rw [Mb_cost]
        exact a.2
      have := lfw_mul_mem (((wd a).map Subtype.val).reverse) h f
      refine (Ideal.span_le.mpr ?_) this
      rintro y ⟨u', hu', rfl⟩
      exact hwords f hf u' (lt_of_le_of_lt (cost_sublist v hv hu') hc)
    · rw [Ideal.span_le]
      rintro y ⟨j, hj, rfl⟩ h
      show Ew B (wd a) (h * G F' (Mb (L.get j).1)) ∈ P
      set b := L.get j with hb
      have hne : b ≠ a := by
        intro hba
        have := (hLnodup.get_inj_iff).mp hba
        rw [Fin.ext_iff] at this
        simp at this
        omega
      have hdeg : deg a ≤ deg b := by
        have := List.pairwise_iff_get.mp hLsorted j ⟨i, hi⟩ (by
          rw [Fin.lt_def]; exact hj)
        exact of_decide_eq_true this
      rcases lt_or_eq_of_le hdeg with hlt | heq
      · have hmem : h * G F' (Mb b.1) ∈ P ^ (1 + (wd a).length) := by
          apply Ideal.mul_mem_left
          apply Ideal.pow_le_pow_right (show 1 + (wd a).length ≤ Multiset.card (Mb b.1) by
            rw [wd_len, Mb_card]; change 1 + deg a ≤ deg b; omega)
          exact G_mem hF' _
        simpa using Ew_pow B P (wd a) 1 _ hmem
      · obtain ⟨c, hciff, hc⟩ := claim hF' hD' (wd a) (Mb b.1)
          (by rw [wd_len, Mb_card, heq]) h
        have hc0 : c = 0 := by
          by_contra hc0
          apply hne
          exact Mb_inj _ _ ((hciff.mpr hc0).symm.trans (wd_coe a)).symm |>.symm
        rw [hc0] at hc
        simpa using hc
  have notmem : ∀ i (hi : i < L.length) (s : MvPolynomial (Fin (m + 1)) ℂ), s ∉ P →
      s * G F' (Mb (L.get ⟨i, hi⟩).1) ∉ W i := by
    intro i hi s hs hmem
    set a := L.get ⟨i, hi⟩ with ha
    have h1 := key i hi hmem 1
    rw [one_mul] at h1
    obtain ⟨c, hciff, hc⟩ := claim hF' hD' (wd a) (Mb a.1)
      (by rw [wd_len, Mb_card]) s
    have hc0 : c ≠ 0 := hciff.mp (wd_coe a)
    have h2 : (c : MvPolynomial (Fin (m + 1)) ℂ) * δ ^ (wd a).length * s ∈ P := by
      convert Ideal.sub_mem _ h1 hc using 1
      ring
    have hcP : (c : MvPolynomial (Fin (m + 1)) ℂ) ∉ P := by
      intro hcm
      apply (Ideal.IsPrime.ne_top ‹P.IsPrime›)
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin (m + 1)) ℂ) =
          (c : MvPolynomial (Fin (m + 1)) ℂ) * MvPolynomial.C ((c : ℂ)⁻¹) := by
        rw [← map_natCast (MvPolynomial.C (σ := Fin (m + 1)) (R := ℂ)), ← map_mul,
          mul_inv_cancel₀ (by exact_mod_cast hc0), map_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ hcm
    rcases (‹P.IsPrime›).mem_or_mem h2 with h3 | h3
    · rcases (‹P.IsPrime›).mem_or_mem h3 with h4 | h4
      · exact hcP h4
      · exact hδ ((‹P.IsPrime›).mem_of_pow_mem _ h4)
    · exact hs h3
  -- Step 4: the strict chain in the localization.
  let A := Localization.AtPrime P
  let V : ℕ → Submodule A A := fun i => (W i).map (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) A)
  let p : LTSeries (Submodule A A) :=
    { length := L.length
      toFun := fun i => V i.val
      step := by
        intro i
        show V i.val < V (i.val + 1)
        refine lt_of_le_of_ne (Ideal.map_mono (sup_le_sup_left (Ideal.span_mono ?_) _)) ?_
        · rintro y ⟨j, hj, rfl⟩
          exact ⟨j, by omega, rfl⟩
        · intro heq
          have hin : algebraMap (MvPolynomial (Fin (m + 1)) ℂ) A
              (G F' (Mb (L.get ⟨i.val, i.2⟩).1)) ∈ V (i.val + 1) :=
            Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨⟨i.val, i.2⟩,
              by simp, rfl⟩))
          rw [← heq] at hin
          obtain ⟨⟨x, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl A).mp hin
          have hinj : G F' (Mb (L.get ⟨i.val, i.2⟩).1) * s = x :=
            IsLocalization.injective A (Ideal.primeCompl_le_nonZeroDivisors P)
              (by rw [map_mul]; exact hx)
          exact notmem i.val i.2 s s.2 (by rw [mul_comm, hinj]; exact x.2) }
  have hhead : (J.map (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) A) : Submodule A A) ≤ p.head := by
    show _ ≤ V 0
    exact Ideal.map_mono le_sup_left
  unfold strictWeightedSimplexCard componentLocalLength
  rw [Module.length_quotient]
  have hcard : Nat.card (FormalInterpolation.strictWeightedSimplex (fun i : B => v i) T) =
      p.length := by
    show Nat.card Sx = L.length
    rw [hLlen]
  rw [hcard]
  exact Order.length_le_coheight hhead

end Aux_OAI_PiExponent_FormalInterpolation_logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity

theorem solution
    {m : Nat} (v : Fin (m + 1) → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (B : Finset (Fin (m + 1)) )
    (hB : LinearIndependent (logarithmicPrimeField P)
      (fun i : B => logarithmicNormalColumnAtPrime P i))
    (hwords : ∀ f ∈ S, ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word < T → logarithmicFrameWord word f ∈ P) :
    (strictWeightedSimplexCard (fun i : B => v i) T : ENat) ≤
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P :=
  Aux_OAI_PiExponent_FormalInterpolation_logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity.main
    v hv T S P B hB hwords
