-- Prove2me | solution 1 for MayersQBC.uhlmann_purification
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T20:57:45.8762+00:00
-- url     : https://prove2.me/submissions/dc5e1d80-b154-4610-9064-fd7bd2d1b2a2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_3
open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

namespace MayersQBCUhlmannAux

/-- The coefficient matrix of `ψ ∈ A ⊗ B`, with Bob's index first: `C b a = ψ (a, b)`. -/
noncomputable def coefB {A B : Type} (ψ : EuclideanSpace ℂ (A × B)) : Matrix B A ℂ :=
  Matrix.of fun b a => ψ (a, b)

lemma traceLeft_pureDensity_eq {A B : Type} [Fintype A] (ψ : EuclideanSpace ℂ (A × B)) :
    traceLeft (pureDensity ψ) = coefB ψ * (coefB ψ)ᴴ := by
  ext b b'
  simp [traceLeft, pureDensity, coefB, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma traceLeft_pureDensity_posSemidef {A B : Type} [Fintype A] [Fintype B]
    (ψ : EuclideanSpace ℂ (A × B)) : (traceLeft (pureDensity ψ)).PosSemidef := by
  rw [traceLeft_pureDensity_eq]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Alice's operation `V ⊗ I` multiplies the coefficient matrix on the right by `Vᵀ`. -/
lemma coefB_act_kronecker {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (V : Matrix A A ℂ) (ψ : EuclideanSpace ℂ (A × B)) :
    coefB (act (Matrix.kronecker V (1 : Matrix B B ℂ)) ψ) = coefB ψ * Vᵀ := by
  ext b a
  simp only [coefB, act, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [mul_comm]
  · intro b'' _ hb''
    simp [Ne.symm hb'']
  · simp

/-- A unitary on Alice's side does not change Bob's reduced state. -/
lemma traceLeft_act_unitary {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (V : Matrix A A ℂ) (hV : V ∈ Matrix.unitaryGroup A ℂ) (ψ : EuclideanSpace ℂ (A × B)) :
    traceLeft (pureDensity (act (Matrix.kronecker V (1 : Matrix B B ℂ)) ψ)) =
      traceLeft (pureDensity ψ) := by
  rw [traceLeft_pureDensity_eq, traceLeft_pureDensity_eq, coefB_act_kronecker,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ]
  have h1 : Vᵀ * (Vᵀ)ᴴ = 1 := by
    have hV' : Vᴴ * V = 1 := by
      have := Matrix.UnitaryGroup.star_mul_self ⟨V, hV⟩
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, ← Matrix.transpose_mul, hV',
      Matrix.transpose_one]
  rw [h1, Matrix.one_mul]

/-- Multiplying by a scalar of modulus one does not change Bob's reduced state. -/
lemma traceLeft_smul_phase {A B : Type} [Fintype A] (ω : ℂ) (hω : ‖ω‖ = 1)
    (ψ : EuclideanSpace ℂ (A × B)) :
    traceLeft (pureDensity (ω • ψ)) = traceLeft (pureDensity ψ) := by
  have hωω : ω * conj ω = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]; simp
  ext b b'
  simp only [traceLeft, pureDensity, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ω * ψ (a, b) * (conj ω * conj (ψ (a, b'))) = (ω * conj ω) * (ψ (a, b) * conj (ψ (a, b'))) := by
        ring
    _ = ψ (a, b) * conj (ψ (a, b')) := by rw [hωω, one_mul]

/-- The overlap appearing in `lemmaB_3` is `⟨ψ0|(U ⊗ I)|ψ1⟩`. -/
lemma overlap_eq_inner {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (U : Matrix A A ℂ) (ψ0 ψ1 : EuclideanSpace ℂ (A × B)) :
    (∑ x : B × A, conj (ψ0 (x.2, x.1)) * ∑ r : A, U x.2 r * ψ1 (r, x.1)) =
      inner ℂ ψ0 (act (Matrix.kronecker U (1 : Matrix B B ℂ)) ψ1) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [act, dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro b'' _ hb''
    simp [Ne.symm hb'']
  · simp

/-- Adjoint relation for `act`: `⟨M x|y⟩ = ⟨x|Mᴴ y⟩`. -/
lemma inner_act_left {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (act M x) y = inner ℂ x (act Mᴴ y) := by
  simp only [act, EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm]

lemma conjTranspose_kronecker_one {A B : Type} [DecidableEq B] (V : Matrix A A ℂ) :
    (Matrix.kronecker V (1 : Matrix B B ℂ))ᴴ = Matrix.kronecker Vᴴ (1 : Matrix B B ℂ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  by_cases h : b = b'
  · subst h
    simp [Matrix.kronecker]
  · have h' : b' ≠ b := Ne.symm h
    simp [Matrix.kronecker, h, h']

/-- The unitary group of square complex matrices is compact. -/
lemma isCompact_unitary (n : Type) [Fintype n] [DecidableEq n] :
    IsCompact (unitary (Matrix n n ℂ) : Set (Matrix n n ℂ)) := by
  have hclosed : IsClosed (unitary (Matrix n n ℂ) : Set (Matrix n n ℂ)) := by
    have hset : (unitary (Matrix n n ℂ) : Set (Matrix n n ℂ)) =
        {U | star U * U = 1} ∩ {U | U * star U = 1} := by
      ext U
      simp [Unitary.mem_iff]
    rw [hset]
    exact (isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const)
  have hK : IsCompact (Set.pi Set.univ fun _ : n =>
      Set.pi Set.univ fun _ : n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset hclosed ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary hU i j

end MayersQBCUhlmannAux

open MayersQBCUhlmannAux in
theorem solution {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ψ0 ψ1 : EuclideanSpace ℂ (A × B)) (h0 : IsState ψ0) (h1 : IsState ψ1) :
    ∃ ψ01 : EuclideanSpace ℂ (A × B), IsState ψ01 ∧
      traceLeft (pureDensity ψ01) = traceLeft (pureDensity ψ0) ∧
      inner ℂ ψ01 ψ1 =
        ((rootFidelity (traceLeft (pureDensity ψ0)) (traceLeft (pureDensity ψ1)) : ℝ) : ℂ) := by
  classical
  -- nonemptiness of the factors (a unit vector exists)
  have hne : Nonempty (A × B) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : ψ0 = 0 := Subsingleton.elim _ _
    have h0' : ‖ψ0‖ = 1 := h0
    rw [this, norm_zero] at h0'
    exact zero_ne_one h0'
  have : Nonempty A := ⟨hne.some.1⟩
  have : Nonempty B := ⟨hne.some.2⟩
  set ρ0 := traceLeft (pureDensity ψ0) with hρ0
  set ρ1 := traceLeft (pureDensity ψ1) with hρ1
  -- the purifications in the convention of `lemmaB_3` (purifying system second)
  let psi : B × A → ℂ := fun x => ψ0 (x.2, x.1)
  let phi : B × A → ℂ := fun x => ψ1 (x.2, x.1)
  have hpur : ∀ ψ : EuclideanSpace ℂ (A × B),
      Papers.Independent.Claimed50.P12.UnnormalizedPurifies (fun x : B × A => ψ (x.2, x.1))
        (traceLeft (pureDensity ψ)) := by
    intro ψ
    ext b b'
    simp [Papers.Independent.Claimed50.P12.vectorOuterProduct, traceRight, traceLeft, pureDensity]
  have hsup := Papers.Independent.Claimed50.P12.lemmaB_3 ρ0 ρ1
    (traceLeft_pureDensity_posSemidef ψ0) (traceLeft_pureDensity_posSemidef ψ1) psi phi
    (hpur ψ0) (hpur ψ1)
  -- the overlap as a continuous function of the unitary
  let g : Matrix A A ℂ → ℝ := fun U =>
    ‖∑ x : B × A, conj (psi x) * ∑ r : A, U x.2 r * phi (x.1, r)‖
  have hg : Continuous g := by
    refine continuous_norm.comp ?_
    refine continuous_finsetSum _ fun x _ => continuous_const.mul ?_
    refine continuous_finsetSum _ fun r _ => ?_
    exact (continuous_id.matrix_elem x.2 r).mul continuous_const
  have hset : {v : ℝ | ∃ U : Matrix.unitaryGroup A ℂ, v =
      ‖∑ x : B × A, conj (psi x) * ∑ r : A, (U : Matrix A A ℂ) x.2 r * phi (x.1, r)‖} =
      g '' (unitary (Matrix A A ℂ) : Set (Matrix A A ℂ)) := by
    ext v
    constructor
    · rintro ⟨U, rfl⟩
      exact ⟨U, U.2, rfl⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨⟨U, hU⟩, rfl⟩
  rw [hset] at hsup
  have hcpt : IsCompact (g '' (unitary (Matrix A A ℂ) : Set (Matrix A A ℂ))) :=
    (isCompact_unitary A).image hg
  have hnonempty : (g '' (unitary (Matrix A A ℂ) : Set (Matrix A A ℂ))).Nonempty :=
    ⟨g 1, 1, one_mem _, rfl⟩
  obtain ⟨U, hU, hUmax⟩ := hcpt.sSup_mem hnonempty
  rw [← hsup] at hUmax
  -- `c = ⟨ψ0|(U ⊗ I)|ψ1⟩` has modulus `rootFidelity ρ0 ρ1`
  set c : ℂ := inner ℂ ψ0 (act (Matrix.kronecker U (1 : Matrix B B ℂ)) ψ1) with hc
  have hcnorm : ‖c‖ = rootFidelity ρ0 ρ1 := by
    rw [← hUmax]
    simp only [g, psi, phi]
    rw [overlap_eq_inner]
  -- the candidate: `χ = (Uᴴ ⊗ I) ψ0`, so that `⟨χ|ψ1⟩ = c`
  set V : Matrix A A ℂ := Uᴴ with hVdef
  have hV : V ∈ Matrix.unitaryGroup A ℂ := by
    have := (⟨U, hU⟩ : Matrix.unitaryGroup A ℂ)⁻¹.2
    simpa [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using this
  set χ := act (Matrix.kronecker V (1 : Matrix B B ℂ)) ψ0 with hχ
  have hχc : inner ℂ χ ψ1 = c := by
    rw [hχ, hc, inner_act_left, conjTranspose_kronecker_one, hVdef,
      Matrix.conjTranspose_conjTranspose]
  have hkron : Matrix.kronecker V (1 : Matrix B B ℂ) ∈ Matrix.unitaryGroup (A × B) ℂ :=
    Matrix.kronecker_mem_unitary hV (one_mem _)
  have hχnorm : ‖χ‖ = 1 := by
    rw [hχ, act_norm_of_mem_unitaryGroup hkron]
    exact h0
  have hχred : traceLeft (pureDensity χ) = ρ0 := by
    rw [hχ, traceLeft_act_unitary V hV]
  -- phase correction
  by_cases hc0 : c = 0
  · refine ⟨χ, hχnorm, hχred, ?_⟩
    rw [hχc, hc0]
    have : rootFidelity ρ0 ρ1 = 0 := by rw [← hcnorm, hc0, norm_zero]
    rw [this]
    simp
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    set ω : ℂ := c / (‖c‖ : ℂ) with hω
    have hωnorm : ‖ω‖ = 1 := by
      rw [hω, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
        div_self hcpos.ne']
    refine ⟨ω • χ, ?_, ?_, ?_⟩
    · show ‖ω • χ‖ = 1
      rw [norm_smul, hωnorm, hχnorm, one_mul]
    · rw [traceLeft_smul_phase ω hωnorm, hχred]
    · rw [inner_smul_left, hχc, hω, ← hcnorm]
      have hc' : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
      rw [map_div₀, Complex.conj_ofReal]
      field_simp
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
