-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.exists_pow_eq_smul_mem_of_mem_normalizer_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T06:11:54.565964+00:00
-- url     : https://prove2.me/submissions/7eef3bb7-ee63-42f7-a5b5-334667dab8c7

import Mathlib

set_option autoImplicit false

/-!
Katz (Arizona notes, pp. 22-23): if `G ≤ GL_n(K)` (`K` algebraically closed) is irreducible and is finite, or contains
`SL_n`, or is `O(B)` / `SO(B)` / `Sp(B)` for a nondegenerate `B`, then a uniform power `φ ^ M` of every `φ` normalising
`G` is a scalar times an element of `G`; hence `φ ^ M` acts trivially on `G`-coinvariants and `G`-invariants of every
representation of `GL_n(K)` trivial on scalars, and eigenvalues of `φ` on the coinvariants are `M`-th roots of unity.
Self-contained (Mathlib only).
-/

namespace UploadFrobScalar

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Scal

/-- The scalar matrices `c • 1` as a monoid hom `Kˣ →* GL_n(K)`. -/
noncomputable def scal : Kˣ →* Matrix.GeneralLinearGroup n K where
  toFun c :=
    { val := (c : K) • 1
      inv := ((c⁻¹ : Kˣ) : K) • 1
      val_inv := by rw [smul_mul_smul_comm, Units.mul_inv, one_smul, Matrix.mul_one]
      inv_val := by rw [smul_mul_smul_comm, Units.inv_mul, one_smul, Matrix.mul_one] }
  map_one' := Units.ext (by
    change ((1 : Kˣ) : K) • (1 : Matrix n n K) = 1
    rw [Units.val_one, one_smul])
  map_mul' a b := Units.ext (by
    change ((a * b : Kˣ) : K) • (1 : Matrix n n K) = ((a : K) • (1 : Matrix n n K)) * ((b : K) • 1)
    rw [smul_mul_smul_comm, Matrix.mul_one, Units.val_mul])

theorem coe_scal (c : Kˣ) : ((scal c : Matrix.GeneralLinearGroup n K) : Matrix n n K) = (c : K) • 1 := rfl

theorem coe_scal_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup n K) :
    ((scal c * g : Matrix.GeneralLinearGroup n K) : Matrix n n K) = (c : K) • (g : Matrix n n K) := by
  rw [Units.val_mul, coe_scal, smul_mul_assoc, Matrix.one_mul]

theorem scal_commute (c : Kˣ) (g : Matrix.GeneralLinearGroup n K) : Commute (scal c) g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_scal, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]

theorem pow_scal_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup n K) (k : ℕ) :
    (scal c * g) ^ k = scal (c ^ k) * g ^ k := by
  rw [(scal_commute c g).mul_pow, map_pow]

/-- A unit of `Matrix n n K` equal to `c • 1` is `scal u`. -/
theorem exists_scal_of_coe_eq {ψ : Matrix.GeneralLinearGroup n K} {c : K}
    (h : (ψ : Matrix n n K) = c • 1) : ∃ u : Kˣ, ψ = scal u := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  · have hc : c ≠ 0 := by
      rintro rfl
      have hu := Units.isUnit ψ
      rw [h, zero_smul] at hu
      exact not_isUnit_zero hu
    exact ⟨Units.mk0 c hc, Units.ext h⟩

end Scal

section Schur

variable [IsAlgClosed K]

/-- Schur: a matrix commuting with an irreducible `G ≤ GL_n(K)` is scalar. -/
theorem eq_smul_one_of_commute {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    {X : Matrix n n K} (hX : ∀ g ∈ G, (g : Matrix n n K) * X = X * g) : ∃ c : K, X = c • 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, Matrix.ext fun i => isEmptyElim i⟩
  · obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' X)
    have hW : ∀ g ∈ G, ∀ v ∈ Module.End.eigenspace (Matrix.toLin' X) c,
        (g : Matrix n n K) *ᵥ v ∈ Module.End.eigenspace (Matrix.toLin' X) c := by
      intro g hg v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, ← hX g hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
    rcases hG _ hW with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
      have hv : v ∈ Module.End.eigenspace (Matrix.toLin' X) c := by rw [h]; exact Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      rw [hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]

end Schur

section ConjPerm

variable {Γ : Type*} [Group Γ]

/-- Conjugation by an element of the normaliser of `H`, as a permutation of `H`. -/
def conjPerm (H : Subgroup Γ) : Subgroup.normalizer (H : Set Γ) →* Equiv.Perm H where
  toFun φ :=
    { toFun := fun h => ⟨(φ : Γ) * h * (φ : Γ)⁻¹, (Subgroup.mem_normalizer_iff.1 φ.2 h).1 h.2⟩
      invFun := fun h => ⟨(φ : Γ)⁻¹ * h * (φ : Γ), (Subgroup.mem_normalizer_iff''.1 φ.2 h).1 h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext h
    simp
  map_mul' a b := by
    ext h
    simp [mul_assoc]

theorem conjPerm_apply (H : Subgroup Γ) (φ : Subgroup.normalizer (H : Set Γ)) (h : H) :
    ((conjPerm H φ h : H) : Γ) = (φ : Γ) * h * (φ : Γ)⁻¹ := rfl

/-- `φ ^ N` centralises `H` for `N = |Perm H|` and every `φ` normalising `H`. -/
theorem pow_card_perm_commute (H : Subgroup Γ) {φ : Γ} (hφ : φ ∈ Subgroup.normalizer (H : Set Γ)) {h : Γ}
    (hh : h ∈ H) :
    φ ^ Nat.card (Equiv.Perm H) * h = h * φ ^ Nat.card (Equiv.Perm H) := by
  have h1 : ((conjPerm H (⟨φ, hφ⟩ ^ Nat.card (Equiv.Perm H)) ⟨h, hh⟩ : H) : Γ) = h := by
    rw [map_pow, pow_card_eq_one']
    rfl
  rw [conjPerm_apply] at h1
  change φ ^ Nat.card (Equiv.Perm H) * h * (φ ^ Nat.card (Equiv.Perm H))⁻¹ = h at h1
  calc φ ^ Nat.card (Equiv.Perm H) * h
      = φ ^ Nat.card (Equiv.Perm H) * h * (φ ^ Nat.card (Equiv.Perm H))⁻¹ * φ ^ Nat.card (Equiv.Perm H) := by
        rw [inv_mul_cancel_right]
    _ = h * φ ^ Nat.card (Equiv.Perm H) := by rw [h1]

end ConjPerm

section Forms

/-- `gᵀ A g = A` ⇒ `(g⁻¹)ᵀ A = A g`. -/
theorem invT_mul_of_iso {A : Matrix n n K} {g : Matrix.GeneralLinearGroup n K}
    (h : (g : Matrix n n K)ᵀ * A * g = A) :
    ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * A = A * g := by
  conv_lhs => rw [← h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.transpose_one, Matrix.one_mul]

theorem iso_mul {B : Matrix n n K} {a b : Matrix.GeneralLinearGroup n K}
    (ha : (a : Matrix n n K)ᵀ * B * a = B) (hb : (b : Matrix n n K)ᵀ * B * b = B) :
    ((a * b : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B *
      ((a * b : Matrix.GeneralLinearGroup n K) : Matrix n n K) = B := by
  rw [Units.val_mul, Matrix.transpose_mul]
  calc (b : Matrix n n K)ᵀ * (a : Matrix n n K)ᵀ * B * ((a : Matrix n n K) * b)
      = (b : Matrix n n K)ᵀ * ((a : Matrix n n K)ᵀ * B * a) * b := by simp only [Matrix.mul_assoc]
    _ = B := by rw [ha, hb]

theorem iso_pow {B : Matrix n n K} {g : Matrix.GeneralLinearGroup n K}
    (hg : (g : Matrix n n K)ᵀ * B * g = B) (k : ℕ) :
    ((g ^ k : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B *
      ((g ^ k : Matrix.GeneralLinearGroup n K) : Matrix n n K) = B := by
  induction k with
  | zero => rw [pow_zero, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  | succ k ih => rw [pow_succ]; exact iso_mul ih hg

theorem det_sq_eq_one {B : Matrix n n K} (hu : IsUnit B.det) {g : Matrix.GeneralLinearGroup n K}
    (hg : (g : Matrix n n K)ᵀ * B * g = B) : ((g ^ 2 : Matrix.GeneralLinearGroup n K) : Matrix n n K).det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  rw [Units.val_pow_eq_pow_val, Matrix.det_pow]
  apply mul_right_cancel₀ hu.ne_zero
  linear_combination h

/-- `φ` normalising `G ≤ O(B)` makes `φᵀ B φ` a `G`-invariant form. -/
theorem conj_form_inv {B : Matrix n n K} {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGB : ∀ g ∈ G, (g : Matrix n n K)ᵀ * B * g = B)
    {φ : Matrix.GeneralLinearGroup n K} (hφ : φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)))
    {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ G) :
    (g : Matrix n n K)ᵀ * ((φ : Matrix n n K)ᵀ * B * φ) * g = (φ : Matrix n n K)ᵀ * B * φ := by
  have hh := hGB _ ((Subgroup.mem_normalizer_iff.1 hφ g).1 hg)
  have e : (φ : Matrix n n K) * g = ((φ * g * φ⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * φ := by
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  calc (g : Matrix n n K)ᵀ * ((φ : Matrix n n K)ᵀ * B * (φ : Matrix n n K)) * (g : Matrix n n K)
      = ((φ : Matrix n n K) * (g : Matrix n n K))ᵀ * B * ((φ : Matrix n n K) * (g : Matrix n n K)) := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (φ : Matrix n n K)ᵀ * (((φ * g * φ⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B *
          ((φ * g * φ⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) * (φ : Matrix n n K) := by
        rw [e, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (φ : Matrix n n K)ᵀ * B * (φ : Matrix n n K) := by rw [hh]

/-- Two `g`-invariant forms `B` (invertible), `B'`: `g` commutes with `B⁻¹ B'`. -/
theorem commute_of_inv_forms {B B' : Matrix n n K} (hu : IsUnit B.det) {g : Matrix.GeneralLinearGroup n K}
    (h1 : (g : Matrix n n K)ᵀ * B * g = B) (h2 : (g : Matrix n n K)ᵀ * B' * g = B') :
    (g : Matrix n n K) * (B⁻¹ * B') = (B⁻¹ * B') * g := by
  have e1 := invT_mul_of_iso h1
  have e2 := invT_mul_of_iso h2
  calc (g : Matrix n n K) * (B⁻¹ * B') = (B⁻¹ * (B * g)) * (B⁻¹ * B') := by
        rw [Matrix.nonsing_inv_mul_cancel_left (A := B) (g : Matrix n n K) hu]
    _ = (B⁻¹ * (((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B)) * (B⁻¹ * B') := by rw [e1]
    _ = B⁻¹ * (((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * (B * (B⁻¹ * B'))) := by
        simp only [Matrix.mul_assoc]
    _ = B⁻¹ * (((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B') := by
        rw [Matrix.mul_nonsing_inv_cancel_left (A := B) B' hu]
    _ = (B⁻¹ * B') * g := by rw [e2, Matrix.mul_assoc]

end Forms

section Cases

variable [IsAlgClosed K]

/-- Finite case: `φ ^ N` is scalar, `N = |Perm G|`. -/
theorem frob_scalar_finite {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    {φ : Matrix.GeneralLinearGroup n K} (hφ : φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K))) :
    ∃ u : Kˣ, φ ^ Nat.card (Equiv.Perm G) = scal u := by
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute hG
    (X := ((φ ^ Nat.card (Equiv.Perm G) : Matrix.GeneralLinearGroup n K) : Matrix n n K))
    (fun g hg => by rw [← Units.val_mul, ← Units.val_mul, pow_card_perm_commute G hφ hg])
  exact exists_scal_of_coe_eq hc

/-- `SL_n ≤ G`: `φ = scal u * g` with `g ∈ G`. -/
theorem frob_scalar_sl {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hSL : ∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).det = 1 → g ∈ G)
    (φ : Matrix.GeneralLinearGroup n K) : ∃ u : Kˣ, ∃ g ∈ G, φ = scal u * g := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · have : IsEmpty n := Fintype.card_eq_zero_iff.1 hn
    exact ⟨1, φ, hSL _ Matrix.det_isEmpty, by rw [map_one, one_mul]⟩
  · obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq ((φ : Matrix n n K).det) hn
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hl
      exact (Matrix.isUnits_det_units φ).ne_zero hl.symm
    refine ⟨Units.mk0 l hl0, scal (Units.mk0 l hl0)⁻¹ * φ, hSL _ ?_, ?_⟩
    · rw [coe_scal_mul, Matrix.det_smul, ← hl, ← mul_pow, Units.val_inv_eq_inv_val, Units.val_mk0,
        inv_mul_cancel₀ hl0, one_pow]
    · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

/-- The normaliser of an irreducible `G ≤ O(B)` consists of similitudes: `φᵀ B φ = c • B`. -/
theorem similitude_of_normalizes {B : Matrix n n K} (hu : IsUnit B.det)
    {G : Subgroup (Matrix.GeneralLinearGroup n K)} (hGB : ∀ g ∈ G, (g : Matrix n n K)ᵀ * B * g = B)
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    {φ : Matrix.GeneralLinearGroup n K} (hφ : φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K))) :
    ∃ c : K, (φ : Matrix n n K)ᵀ * B * φ = c • B := by
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute hG (X := B⁻¹ * ((φ : Matrix n n K)ᵀ * B * φ))
    (fun g hg => commute_of_inv_forms hu (hGB g hg) (conj_form_inv hGB hφ hg))
  refine ⟨c, ?_⟩
  calc (φ : Matrix n n K)ᵀ * B * φ = B * (B⁻¹ * ((φ : Matrix n n K)ᵀ * B * φ)) :=
        (Matrix.mul_nonsing_inv_cancel_left (A := B) _ hu).symm
    _ = c • B := by rw [hc, Matrix.mul_smul, Matrix.mul_one]

/-- A similitude `φᵀ B φ = c • B` is `scal u * g` with `gᵀ B g = B`. -/
theorem exists_iso_of_similitude {B : Matrix n n K} (hu : IsUnit B.det) {φ : Matrix.GeneralLinearGroup n K}
    {c : K} (hc : (φ : Matrix n n K)ᵀ * B * φ = c • B) :
    ∃ u : Kˣ, ∃ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K)ᵀ * B * g = B ∧ φ = scal u * g := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, φ, Matrix.ext fun i => isEmptyElim i, by rw [map_one, one_mul]⟩
  · have hc0 : c ≠ 0 := by
      rintro rfl
      have hd := congrArg Matrix.det hc
      rw [zero_smul, Matrix.det_zero, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
      have h1 := Matrix.isUnits_det_units φ
      exact ((h1.mul hu).mul h1).ne_zero hd
    obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hc0 (by rw [← hl]; ring)
    refine ⟨Units.mk0 l hl0, scal (Units.mk0 l hl0)⁻¹ * φ, ?_, ?_⟩
    · have e : ((scal (Units.mk0 l hl0)⁻¹ * φ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B *
          ((scal (Units.mk0 l hl0)⁻¹ * φ : Matrix.GeneralLinearGroup n K) : Matrix n n K) =
          ((((Units.mk0 l hl0)⁻¹ : Kˣ) : K) * (((Units.mk0 l hl0)⁻¹ : Kˣ) : K)) •
            ((φ : Matrix n n K)ᵀ * B * φ) := by
        rw [coe_scal_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [e, hc, smul_smul, ← hl, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
    · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

/-- Katz pp.22-23: a uniform `M > 0` with `φ ^ M = scal u * g`, `g ∈ G`, for every `φ` normalising `G`. -/
theorem frob_scalar {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcase : Finite G ∨
      (∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).det = 1 → g ∈ G) ∨
      ∃ B : Matrix n n K, B.Nondegenerate ∧
        ((∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B) ∨
          (∀ g : Matrix.GeneralLinearGroup n K,
            g ∈ G ↔ (Matrix.transpose (g : Matrix n n K) * B * g = B ∧ (g : Matrix n n K).det = 1)))) :
    ∃ M : ℕ, 0 < M ∧ ∀ φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)),
      ∃ u : Kˣ, ∃ g ∈ G, φ ^ M = scal u * g := by
  rcases hcase with hfin | hSL | ⟨B, hnd, hB⟩
  · refine ⟨Nat.card (Equiv.Perm G), Nat.card_pos, fun φ hφ => ?_⟩
    obtain ⟨u, hu⟩ := frob_scalar_finite hG hφ
    exact ⟨u, 1, G.one_mem, by rw [hu, mul_one]⟩
  · refine ⟨1, one_pos, fun φ _ => ?_⟩
    rw [pow_one]
    exact frob_scalar_sl hSL φ
  · have hu : IsUnit B.det := isUnit_iff_ne_zero.2 (Matrix.nondegenerate_iff_det_ne_zero.1 hnd)
    have hGB : ∀ g ∈ G, (g : Matrix n n K)ᵀ * B * g = B := by
      intro g hg
      rcases hB with h | h
      · exact (h g).1 hg
      · exact ((h g).1 hg).1
    refine ⟨2, two_pos, fun φ hφ => ?_⟩
    obtain ⟨c, hc⟩ := similitude_of_normalizes hu hGB hG hφ
    obtain ⟨u, g, hg, rfl⟩ := exists_iso_of_similitude hu hc
    refine ⟨u ^ 2, g ^ 2, ?_, pow_scal_mul u g 2⟩
    rcases hB with h | h
    · exact (h _).2 (iso_pow hg 2)
    · exact (h _).2 ⟨iso_pow hg 2, det_sq_eq_one hu hg⟩

end Cases

section Rep

/-- `φ` normalising `G` preserves the span of the `ρ g u - u`. -/
theorem coinv_le_comap {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Matrix.GeneralLinearGroup n K →* Module.End K W) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    {φ : Matrix.GeneralLinearGroup n K} (hφ : φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K))) :
    Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} ≤
      (Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u}).comap (ρ φ) := by
  rw [Submodule.span_le]
  rintro w ⟨g, hg, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  apply Submodule.subset_span
  refine ⟨φ * g * φ⁻¹, (Subgroup.mem_normalizer_iff.1 hφ g).1 hg, ρ φ v, ?_⟩
  have e : ρ (φ * g * φ⁻¹) * ρ φ = ρ φ * ρ g := by rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have e' : ρ (φ * g * φ⁻¹) (ρ φ v) = ρ φ (ρ g v) := LinearMap.congr_fun e v
  rw [map_sub, e']

/-- If `ρ φ v ≡ μ v` modulo a `ρ φ`-stable submodule `C`, then `ρ (φ ^ k) v ≡ μ ^ k v`. -/
theorem pow_sub_mem {W : Type*} [AddCommGroup W] [Module K W] (f : Module.End K W) (C : Submodule K W)
    (hC : C ≤ C.comap f) {μ : K} {v : W} (hμ : f v - μ • v ∈ C) (k : ℕ) : (f ^ k) v - μ ^ k • v ∈ C := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Module.End.one_apply, one_smul, sub_self]
    exact C.zero_mem
  | succ k ih =>
    have e : (f ^ (k + 1)) v - μ ^ (k + 1) • v = f ((f ^ k) v - μ ^ k • v) + μ ^ k • (f v - μ • v) := by
      rw [pow_succ' f k, Module.End.mul_apply, map_sub, map_smul, smul_sub, smul_smul, ← pow_succ]
      abel
    rw [e]
    exact C.add_mem (hC ih) (C.smul_mem _ hμ)

end Rep

theorem main {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] [IsAlgClosed K]
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcase : Finite G ∨
      (∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).det = 1 → g ∈ G) ∨
      ∃ B : Matrix n n K, B.Nondegenerate ∧
        ((∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B) ∨
          (∀ g : Matrix.GeneralLinearGroup n K,
            g ∈ G ↔ (Matrix.transpose (g : Matrix n n K) * B * g = B ∧ (g : Matrix n n K).det = 1)))) :
    ∃ M : ℕ, 0 < M ∧
      (∀ φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)),
        ∃ c : K, ∃ g ∈ G, ((φ ^ M : Matrix.GeneralLinearGroup n K) : Matrix n n K) = c • (g : Matrix n n K)) ∧
      ∀ (W : Type*) [AddCommGroup W] [Module K W] (ρ : Matrix.GeneralLinearGroup n K →* Module.End K W),
        (∀ (s : Matrix.GeneralLinearGroup n K) (c : K), (s : Matrix n n K) = c • (1 : Matrix n n K) → ρ s = 1) →
        ∀ φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)),
          (∀ v : W, ρ (φ ^ M) v - v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u}) ∧
          (∀ v : W, (∀ g ∈ G, ρ g v = v) → ρ (φ ^ M) v = v) ∧
          ∀ (μ : K) (v : W), v ∉ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} →
            ρ φ v - μ • v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} → μ ^ M = 1 := by
  obtain ⟨M, hM, hfr⟩ := frob_scalar hG hcase
  refine ⟨M, hM, fun φ hφ => ?_, fun W _ _ ρ hρ φ hφ => ?_⟩
  · obtain ⟨u, g, hg, h⟩ := hfr φ hφ
    exact ⟨u, g, hg, by rw [h, coe_scal_mul]⟩
  · obtain ⟨u, g, hg, h⟩ := hfr φ hφ
    have hs : ρ (scal u) = 1 := hρ _ (u : K) (coe_scal u)
    have hpow : ρ (φ ^ M) = ρ g := by rw [h, map_mul, hs, one_mul]
    have hmem : ∀ v : W, ρ (φ ^ M) v - v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} := by
      intro v
      rw [hpow]
      exact Submodule.subset_span ⟨g, hg, v, rfl⟩
    refine ⟨hmem, fun v hv => ?_, fun μ v hv hμ => ?_⟩
    · rw [hpow]
      exact hv g hg
    · have h1 := pow_sub_mem (ρ φ) _ (coinv_le_comap ρ hφ) hμ M
      rw [← map_pow] at h1
      have h2 := Submodule.sub_mem _ (hmem v) h1
      by_contra hne
      have h4 : (μ ^ M - 1 : K) ≠ 0 := sub_ne_zero.2 hne
      have h3 : (μ ^ M - 1 : K) • v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} := by
        have e : (ρ (φ ^ M) v - v) - (ρ (φ ^ M) v - μ ^ M • v) = (μ ^ M - 1 : K) • v := by
          rw [sub_smul, one_smul]
          abel
        rw [← e]
        exact h2
      apply hv
      have h5 := Submodule.smul_mem _ (μ ^ M - 1 : K)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ h4, one_smul] at h5

end UploadFrobScalar

theorem solution
    {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] [IsAlgClosed K]
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcase : Finite G ∨
      (∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).det = 1 → g ∈ G) ∨
      ∃ B : Matrix n n K, B.Nondegenerate ∧
        ((∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B) ∨
          (∀ g : Matrix.GeneralLinearGroup n K,
            g ∈ G ↔ (Matrix.transpose (g : Matrix n n K) * B * g = B ∧ (g : Matrix n n K).det = 1)))) :
    ∃ M : ℕ, 0 < M ∧
      (∀ φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)),
        ∃ c : K, ∃ g ∈ G, ((φ ^ M : Matrix.GeneralLinearGroup n K) : Matrix n n K) = c • (g : Matrix n n K)) ∧
      ∀ (W : Type*) [AddCommGroup W] [Module K W] (ρ : Matrix.GeneralLinearGroup n K →* Module.End K W),
        (∀ (s : Matrix.GeneralLinearGroup n K) (c : K), (s : Matrix n n K) = c • (1 : Matrix n n K) → ρ s = 1) →
        ∀ φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)),
          (∀ v : W, ρ (φ ^ M) v - v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u}) ∧
          (∀ v : W, (∀ g ∈ G, ρ g v = v) → ρ (φ ^ M) v = v) ∧
          ∀ (μ : K) (v : W), v ∉ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} →
            ρ φ v - μ • v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} → μ ^ M = 1 := by
  exact UploadFrobScalar.main G hG hcase
