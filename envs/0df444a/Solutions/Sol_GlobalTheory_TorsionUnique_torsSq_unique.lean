-- Prove2me | solution 1 for GlobalTheory.TorsionUnique.torsSq_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:24:49.885316+00:00
-- url     : https://prove2.me/submissions/e1ce12d0-91cc-48f8-8f4c-0cd8056fe123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.KeyKa
namespace GlobalTheory.TorsionUnique
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] in
private lemma submatrix_mul_eq_of_vanishing_off {ι κ : Type} (X Y : Matrix Ix Ix R) (Q : Ix → Prop)
    [DecidablePred Q] (f : ι → Ix) (g : κ → Ix) (hX : ∀ i r, ¬ Q r → X (f i) r = 0) :
    (X * Y).submatrix f g
      = X.submatrix f (Subtype.val : {r // Q r} → Ix) * Y.submatrix Subtype.val g := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype Q,
    Finset.sum_eq_zero (s := (Finset.univ : Finset {r // ¬ Q r}))
      (fun r _ => by rw [hX i r r.2, zero_mul]), add_zero]
  rfl
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] in
private lemma apply_eq_zero_of_hasDeg_odd_of_even_even {deg : Ix → ℕ} {k : ℤ} {X : Matrix Ix Ix R}
    (hX : _root_.GlobalTheory.TorsionUnique.HasDeg deg k X) (hk : k = 1 ∨ k = -1) {p q : Ix}
    (hp : Even (deg p)) (hq : Even (deg q)) : X p q = 0 := by
  rw [Nat.even_iff] at hp hq
  exact hX p q (by omega)
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] in
private lemma hasDeg_mul {deg : Ix → ℕ} {a b c : ℤ} {X Y : Matrix Ix Ix R}
    (hX : _root_.GlobalTheory.TorsionUnique.HasDeg deg a X) (hY : _root_.GlobalTheory.TorsionUnique.HasDeg deg b Y)
    (hc : a + b = c) : _root_.GlobalTheory.TorsionUnique.HasDeg deg c (X * Y) := by
  intro p q hpq
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : (deg p : ℤ) = deg r + a
  · rw [hY r q (by omega), mul_zero]
  · rw [hX p r hr, zero_mul]
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] in
private lemma hasDeg_sub {deg : Ix → ℕ} {a : ℤ} {X Y : Matrix Ix Ix R}
    (hX : _root_.GlobalTheory.TorsionUnique.HasDeg deg a X) (hY : _root_.GlobalTheory.TorsionUnique.HasDeg deg a Y) :
    _root_.GlobalTheory.TorsionUnique.HasDeg deg a (X - Y) := by
  intro p q hpq
  rw [Matrix.sub_apply, hX p q hpq, hY p q hpq, sub_zero]
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] in
private lemma det_one_add_sub_mul_degree_submatrix_eq_one (deg : Ix → ℕ) (D h₁ h₂ : Matrix Ix Ix R)
    (hD : _root_.GlobalTheory.TorsionUnique.HasDeg deg (-1) D) (hDD : D * D = 0)
    (h₁d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₁) (h₂d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₂)
    (h₁c : D * h₁ + h₁ * D = 1) (h₂c : D * h₂ + h₂ * D = 1) (d : ℕ) :
    (((1 : Matrix Ix Ix R) + (h₂ - h₁) * D).submatrix (Subtype.val : {p // deg p = d} → Ix)
      Subtype.val).det = 1 := by
  set k := h₂ - h₁ with hk_def
  have hkd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 k := hasDeg_sub h₂d h₁d
  have hψd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 0 (k * D) := hasDeg_mul hkd hD (by norm_num)
  have hkD : D * k + k * D = 0 := by
    have : D * k + k * D = (D * h₂ + h₂ * D) - (D * h₁ + h₁ * D) := by
      simp only [hk_def, mul_sub, sub_mul]; abel
    rw [this, h₁c, h₂c, sub_self]
  have hDk : D * k = -(k * D) := eq_neg_of_add_eq_zero_left hkD
  have hψψ : k * D * (k * D) = 0 := by
    calc k * D * (k * D) = k * (D * k) * D := by simp only [mul_assoc]
      _ = -(k * k * (D * D)) := by rw [hDk]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = 0 := by rw [hDD]; simp
  have hblock : ∀ n : ℕ, ((1 : Matrix Ix Ix R) + k * D).submatrix
      (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        = 1 + (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix)
          (Subtype.val : {p // deg p = n} → Ix) := by
    intro n
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Subtype.val_injective.ne hij)]
  induction d with
  | zero =>
    rw [hblock]
    have : (k * D).submatrix (Subtype.val : {p // deg p = 0} → Ix) (Subtype.val : {p // deg p = 0} → Ix) = 0 := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [hD r j (by have := j.2; omega), mul_zero]
    rw [this, add_zero, Matrix.det_one]
  | succ n ih =>
    rw [hblock] at ih ⊢
    have hsplit : (k * D).submatrix (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n + 1} → Ix)
        = k.submatrix (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n} → Ix)
          * D.submatrix (Subtype.val : {p // deg p = n} → Ix)
            (Subtype.val : {p // deg p = n + 1} → Ix) :=
      submatrix_mul_eq_of_vanishing_off k D (fun r => deg r = n) (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n + 1} → Ix)
        (fun i r hr => hkd _ r (by have := i.2; omega))
    have hswap : D.submatrix (Subtype.val : {p // deg p = n} → Ix)
          (Subtype.val : {p // deg p = n + 1} → Ix)
          * k.submatrix (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        = -(k * D).submatrix (Subtype.val : {p // deg p = n} → Ix)
          (Subtype.val : {p // deg p = n} → Ix) := by
      exact (submatrix_mul_eq_of_vanishing_off D k (fun r => deg r = n + 1) (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        (fun i r hr => hD _ r (by have := i.2; omega))).symm.trans (by rw [hDk, Matrix.submatrix_neg]; rfl)
    have hsq : (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
          * (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix)
            (Subtype.val : {p // deg p = n} → Ix) = 0 := by
      exact (submatrix_mul_eq_of_vanishing_off (k * D) (k * D) (fun r => deg r = n) (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        (fun i r hr => hψd _ r (by have := i.2; omega))).symm.trans (by rw [hψψ, Matrix.submatrix_zero]; rfl)
    set ψ := (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
    have hinv : (1 - ψ).det * (1 + ψ).det = 1 := by
      rw [← Matrix.det_mul, sub_mul, one_mul, mul_add, mul_one, hsq]; simp
    rw [hsplit, Matrix.det_one_add_mul_comm, hswap, ← sub_eq_add_neg]
    rw [ih, mul_one] at hinv
    exact hinv
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] in
private lemma det_even_submatrix_homotopy_product_eq_one (deg : Ix → ℕ) (D h₁ h₂ : Matrix Ix Ix R)
    (hD : _root_.GlobalTheory.TorsionUnique.HasDeg deg (-1) D) (hDD : D * D = 0)
    (h₁d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₁) (h₂d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₂)
    (h₁c : D * h₁ + h₁ * D = 1) (h₂c : D * h₂ + h₂ * D = 1) :
    (((D + h₂) * (D + h₁)).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
      Subtype.val).det = 1 := by
  have hG : (D + h₂) * (D + h₁) = 1 + (h₂ - h₁) * D + h₂ * h₁ := by
    have e₁ : D * h₁ = 1 - h₁ * D := eq_sub_of_add_eq h₁c
    rw [add_mul, mul_add, mul_add, hDD, e₁, sub_mul]; abel
  have hψd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 0 ((h₂ - h₁) * D) :=
    hasDeg_mul (hasDeg_sub h₂d h₁d) hD (by norm_num)
  have hhd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 2 (h₂ * h₁) := hasDeg_mul h₂d h₁d (by norm_num)
  have hlow : ∀ p q, deg p < deg q → ((D + h₂) * (D + h₁)) p q = 0 := by
    intro p q hpq
    rw [hG, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply_ne (by rintro rfl; omega),
      hψd p q (by omega), hhd p q (by omega)]
    simp
  have hdiag : ∀ p q, deg p = deg q →
      ((D + h₂) * (D + h₁)) p q = ((1 : Matrix Ix Ix R) + (h₂ - h₁) * D) p q := by
    intro p q hpq
    rw [hG, Matrix.add_apply (1 + _), hhd p q (by omega), add_zero]
  set M := ((D + h₂) * (D + h₁)).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
    Subtype.val
  have htri : Matrix.BlockTriangular M.transpose (fun i => deg i.1) := by
    intro i j hij
    exact hlow _ _ hij
  rw [← Matrix.det_transpose, htri.det]
  refine Finset.prod_eq_one fun d _ => ?_
  by_cases hd : Even d
  · let E : {i : {p // Even (deg p)} // deg i.1 = d} ≃ {p : Ix // deg p = d} :=
      { toFun := fun i => ⟨i.1.1, i.2⟩
        invFun := fun p => ⟨⟨p.1, by rw [p.2]; exact hd⟩, p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have : M.transpose.toSquareBlock (fun i => deg i.1) d
        = (((1 : Matrix Ix Ix R) + (h₂ - h₁) * D).submatrix
            (Subtype.val : {p // deg p = d} → Ix) Subtype.val).transpose.submatrix E E := by
      ext i j
      simp only [Matrix.toSquareBlock, Matrix.submatrix_apply, Matrix.transpose_apply, M, E,
        Equiv.coe_fn_mk]
      exact hdiag _ _ (by rw [i.2, j.2])
    rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact det_one_add_sub_mul_degree_submatrix_eq_one deg D h₁ h₂ hD hDD h₁d h₂d h₁c h₂c d
  · haveI : IsEmpty {i : {p // Even (deg p)} // deg i.1 = d} :=
      ⟨fun i => hd (by rw [← i.2]; exact i.1.2)⟩
    exact Matrix.det_isEmpty
end GlobalTheory.TorsionUnique
end

set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionUnique
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsionUnique
namespace _root_.GlobalTheory.TorsionUnique
theorem _root_.solution : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix]
    (deg : Ix → ℕ) (D : Matrix Ix Ix R) (t t' : R),
    _root_.GlobalTheory.KeyKa.IsCx deg D → _root_.GlobalTheory.KeyKa.TorsSq deg D t →
      _root_.GlobalTheory.KeyKa.TorsSq deg D t' → t = t' ∧ IsUnit t := by
  intro R Ix _ _ _ deg D t t' hDiff H H'
  obtain ⟨h, hh, hc, e, rfl⟩ := H
  obtain ⟨h', hh', hc', e', rfl⟩ := H'
  have hDiff' := hDiff
  unfold _root_.GlobalTheory.KeyKa.IsCx at hDiff'
  obtain ⟨hD0, hDD⟩ := hDiff'
  have hD : _root_.GlobalTheory.TorsionUnique.HasDeg deg (-1) D := fun p q hpq => hD0 p q (by omega)
  have hd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h := fun p q hpq => hh p q (by omega)
  have hd' : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h' := fun p q hpq => hh' p q (by omega)
  have hprod : ∀ g : Matrix Ix Ix R, _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 g →
      ((D + g).submatrix (Subtype.val : {p // Even (deg p)} → Ix) (fun p => (e' p : Ix))
        * (D + h).submatrix (fun p => (e' p : Ix)) Subtype.val)
        = ((D + g) * (D + h)).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
          (Subtype.val : {p // Even (deg p)} → Ix) := by
    intro g hg
    rw [submatrix_mul_eq_of_vanishing_off (D + g) (D + h) (fun r => ¬ Even (deg r)) _ _
      (fun i r hr => by
        rw [not_not] at hr
        rw [Matrix.add_apply, apply_eq_zero_of_hasDeg_odd_of_even_even hD (Or.inr rfl) i.2 hr,
          apply_eq_zero_of_hasDeg_odd_of_even_even hg (Or.inl rfl) i.2 hr, add_zero])]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e' (fun r => (D + g) i.1 r.1 * (D + h) r.1 j.1)
  set c := ((D + h).submatrix (fun p => (e' p : Ix))
    (Subtype.val : {p // Even (deg p)} → Ix)).det
  set a := ((D + h).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
    (fun p => (e' p : Ix))).det
  set b := ((D + h').submatrix (Subtype.val : {p // Even (deg p)} → Ix)
    (fun p => (e' p : Ix))).det
  have hac : a * c = 1 := by
    rw [← Matrix.det_mul, hprod h hd]
    exact det_even_submatrix_homotopy_product_eq_one deg D h h hD hDD hd hd hc hc
  have hbc : b * c = 1 := by
    rw [← Matrix.det_mul, hprod h' hd']
    exact det_even_submatrix_homotopy_product_eq_one deg D h h' hD hDD hd hd' hc hc'
  have hba : b = a := by
    calc b = b * (a * c) := by rw [hac, mul_one]
      _ = a * (b * c) := by ring
      _ = a := by rw [hbc, mul_one]
  have hsq : ∀ (g : Matrix Ix Ix R) (f : {p // Even (deg p)} ≃ {p // ¬ Even (deg p)}),
      ((g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) fun p => (f p : Ix)).det) ^ 2
        = ((g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) fun p => (e' p : Ix)).det) ^ 2 := by
    intro g f
    have : g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) (fun p => (f p : Ix))
        = (g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) fun p => (e' p : Ix)).submatrix id
          (f.trans e'.symm) := by
      ext i j
      simp
    rw [this, Matrix.det_permute', mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (f.trans e'.symm)) with hs | hs <;> simp [hs]
  refine ⟨?_, ?_⟩
  · rw [hsq (D + h) e, hsq (D + h') e']
    change a ^ 2 = b ^ 2
    rw [hba]
  · rw [hsq (D + h) e]
    have ha : IsUnit a := ⟨⟨a, c, hac, by rw [mul_comm]; exact hac⟩, rfl⟩
    exact ha.pow 2
end _root_.GlobalTheory.TorsionUnique
end GlobalTheory.TorsionUnique
