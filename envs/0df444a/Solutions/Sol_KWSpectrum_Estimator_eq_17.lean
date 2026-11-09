-- Prove2me | solution 1 for KWSpectrum.Estimator.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T05:21:03.065816+00:00
-- url     : https://prove2.me/submissions/8240b9d9-c75d-4222-b7e0-0db175936735

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped Matrix

namespace KW17Aux
open QAlgorithms QAlgorithms.Schur

attribute [local instance] Classical.propDecidable

variable {d n : ℕ}

/-- tensor permutation entries, reversed condition. -/
lemma tp_apply (g : Equiv.Perm (Fin n)) (y x : Fin n → Fin d) :
    tensorPermutation d n g y x = if x = y ∘ g then 1 else 0 := by
  simp only [tensorPermutation, Matrix.of_apply]
  have h : (y = x ∘ g.symm) ↔ (x = y ∘ g) := by
    constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  by_cases hx : x = y ∘ g
  · rw [if_pos (h.mpr hx), if_pos hx]
  · rw [if_neg (fun h' => hx (h.mp h')), if_neg hx]

lemma tp_mul (g h : Equiv.Perm (Fin n)) :
    tensorPermutation d n g * tensorPermutation d n h = tensorPermutation d n (g * h) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (y ∘ g)]
  · rw [tp_apply, tp_apply, tp_apply, if_pos rfl, one_mul, Equiv.Perm.coe_mul]
    rfl
  · intro b _ hb; rw [tp_apply, if_neg (fun e => hb e), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma tp_one : tensorPermutation d n 1 = 1 := by
  ext y x; rfl

lemma piKron_comm (ρ : Matrix (Fin d) (Fin d) ℂ) (g : Equiv.Perm (Fin n)) :
    piKron n ρ * tensorPermutation d n g = tensorPermutation d n g * piKron n ρ := by
  ext y x
  have hL : (piKron n ρ * tensorPermutation d n g) y x = piKron n ρ y (x ∘ g.symm) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (x ∘ g.symm)]
    · rw [tp_apply, if_pos (by funext i; simp), mul_one]
    · intro b _ hb
      rw [tp_apply, if_neg, mul_zero]
      rintro rfl
      exact hb (by funext i; simp)
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : (tensorPermutation d n g * piKron n ρ) y x = piKron n ρ (y ∘ g) x := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (y ∘ g)]
    · rw [tp_apply, if_pos rfl, one_mul]
    · intro b _ hb; rw [tp_apply, if_neg (fun e => hb e), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR]
  simp only [piKron, Matrix.of_apply, Function.comp_apply]
  rw [← Equiv.prod_comp g (fun i => ρ (y i) (x (g.symm i)))]
  simp

/-- group-algebra image on tensor space. -/
def Phi (d n : ℕ) (v : Equiv.Perm (Fin n) → ℂ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ g, v g • tensorPermutation d n g

lemma tensorYoung_comm (Y : Partition d n) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    piKron n ρ * tensorYoungOperator Y = tensorYoungOperator Y * piKron n ρ := by
  simp only [tensorYoungOperator, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, piKron_comm]

lemma Phi_comm (v : Equiv.Perm (Fin n) → ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    piKron n ρ * Phi d n v = Phi d n v * piKron n ρ := by
  simp only [Phi, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, piKron_comm]

/-- the Young element as a function. -/
def cY (Y : Partition d n) : Equiv.Perm (Fin n) → ℂ := fun g => youngRightOperator Y g 1

lemma Phi_R (Y : Partition d n) (x : Equiv.Perm (Fin n) → ℂ) :
    Phi d n (youngRightOperator Y *ᵥ x) = Phi d n x * tensorYoungOperator Y := by
  have hR : Phi d n x * tensorYoungOperator Y = ∑ h, ∑ a ∈ rowPermutations Y,
      ∑ b ∈ columnPermutations Y,
        (x h * (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ)) • tensorPermutation d n (h * (a * b)) := by
    rw [Phi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [tensorYoungOperator, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, tp_mul]
  rw [hR]
  simp only [Phi, Matrix.mulVec, dotProduct, youngRightOperator, Matrix.of_apply, Finset.sum_mul,
    Finset.sum_smul, Int.cast_ite, Int.cast_zero]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ite_mul, zero_mul, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, mul_assoc, mul_comm]

lemma Phi_cY (Y : Partition d n) : Phi d n (cY Y) = tensorYoungOperator Y := by
  have h1 : cY Y = youngRightOperator Y *ᵥ (Pi.single 1 1) := by
    funext g
    simp [cY, Matrix.mulVec_single]
  have h2 : Phi d n (Pi.single 1 1) = 1 := by
    rw [Phi, Finset.sum_eq_single 1]
    · simp [tp_one]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, Phi_R, h2, Matrix.one_mul]

lemma Phi_conv (u v : Equiv.Perm (Fin n) → ℂ) :
    Phi d n u * Phi d n v = Phi d n (fun g => ∑ h, u h * v (h⁻¹ * g)) := by
  simp only [Phi, Finset.sum_mul_sum, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    tp_mul]
  rw [mul_comm (v s)]

/-- conjugation invariance of the tensor character. -/
lemma trace_conj (ρ : Matrix (Fin d) (Fin d) ℂ) (g π : Equiv.Perm (Fin n)) :
    (piKron n ρ * tensorPermutation d n (g⁻¹ * π * g)).trace =
      (piKron n ρ * tensorPermutation d n π).trace := by
  rw [← tp_mul, ← tp_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, piKron_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, tp_mul, mul_inv_cancel, tp_one, Matrix.mul_one]

section Proj

/-- left translation isometry on the regular space. -/
def Lt (h : Equiv.Perm (Fin n)) :
    EuclideanSpace ℂ (Equiv.Perm (Fin n)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Equiv.Perm (Fin n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft h)

lemma Lt_apply (h : Equiv.Perm (Fin n)) (v : EuclideanSpace ℂ (Equiv.Perm (Fin n)))
    (g : Equiv.Perm (Fin n)) : Lt h v g = v (h⁻¹ * g) := by
  simp [Lt, Equiv.piCongrLeft'_apply]

lemma tel_apply {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) (g : ι) :
    Matrix.toEuclideanLin M v g = ∑ k, M g k * v k := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

lemma lin_mul_apply {ι : Type} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) = Matrix.toEuclideanLin (M * N) v := by
  rw [Matrix.toLpLin_mul_same]; rfl

lemma R_left (Y : Partition d n) (g k h : Equiv.Perm (Fin n)) :
    youngRightOperator Y g (h * k) = youngRightOperator Y (h⁻¹ * g) k := by
  simp only [youngRightOperator, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e : (g = h * k * a * b) ↔ (h⁻¹ * g = k * a * b) := by
    simp only [mul_assoc, inv_mul_eq_iff_eq_mul]
  by_cases hc : g = h * k * a * b
  · rw [if_pos hc, if_pos (e.mp hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (e.mpr h'))]

lemma R_Lt (Y : Partition d n) (h : Equiv.Perm (Fin n)) (v : EuclideanSpace ℂ (Equiv.Perm (Fin n))) :
    Lt h (Matrix.toEuclideanLin (youngRightOperator Y) v) =
      Matrix.toEuclideanLin (youngRightOperator Y) (Lt h v) := by
  ext g
  rw [Lt_apply, tel_apply, tel_apply]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.coe_mulLeft, Lt_apply, inv_mul_cancel_left, R_left]

lemma S_map (Y : Partition d n) (h : Equiv.Perm (Fin n)) :
    (spechtSpace Y).map ((Lt h).toLinearEquiv : _ →ₗ[ℂ] _) = spechtSpace Y := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨Lt h v, (R_Lt Y h v).symm⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨Matrix.toEuclideanLin (youngRightOperator Y) ((Lt h).symm v), ⟨_, rfl⟩, ?_⟩
    show Lt h (Matrix.toEuclideanLin (youngRightOperator Y) ((Lt h).symm v)) = _
    rw [R_Lt, LinearIsometryEquiv.apply_symm_apply]

lemma P_Lt (Y : Partition d n) (h : Equiv.Perm (Fin n))
    (w : EuclideanSpace ℂ (Equiv.Perm (Fin n))) :
    (spechtSpace Y).starProjection (Lt h w) = Lt h ((spechtSpace Y).starProjection w) := by
  have := Submodule.starProjection_map_apply (Lt h) (spechtSpace Y) (Lt h w)
  have key : ∀ (K : Submodule ℂ (EuclideanSpace ℂ (Equiv.Perm (Fin n))))
      [K.HasOrthogonalProjection], K = spechtSpace Y →
      K.starProjection (Lt h w) = (spechtSpace Y).starProjection (Lt h w) := by
    intro K _ hK; subst hK; rfl
  rw [key _ (S_map Y h)] at this
  simpa using this

lemma ket_Lt (h : Equiv.Perm (Fin n)) :
    (ket h : EuclideanSpace ℂ (Equiv.Perm (Fin n))) = Lt h (ket 1) := by
  ext g
  rw [Lt_apply]
  simp only [ket, EuclideanSpace.single_apply, inv_mul_eq_one]
  by_cases hg : g = h
  · subst hg; simp
  · rw [if_neg hg, if_neg (fun e => hg e.symm)]

/-- first column of the Specht projection. -/
def qY (Y : Partition d n) : Equiv.Perm (Fin n) → ℂ :=
  fun g => (spechtSpace Y).starProjection (ket 1) g

lemma Pket_apply (Y : Partition d n) (h g : Equiv.Perm (Fin n)) :
    (spechtSpace Y).starProjection (ket h) g = qY Y (h⁻¹ * g) := by
  rw [ket_Lt, P_Lt, Lt_apply]; rfl

lemma Q_apply (Y : Partition d n) (g h : Equiv.Perm (Fin n)) :
    spechtProjection Y g h = qY Y (h⁻¹ * g) := by
  rw [← Pket_apply]
  simp [spechtProjection, ket, EuclideanSpace.inner_single_left]

lemma char_inv (Y : Partition d n) (π : Equiv.Perm (Fin n)) :
    spechtCharacter Y π⁻¹ = ∑ g, qY Y (g⁻¹ * π * g) := by
  simp only [spechtCharacter, Matrix.trace, Matrix.diag, Matrix.mul_apply, leftRegular,
    Matrix.of_apply, ite_mul, one_mul, zero_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single (π * g)]
  · rw [if_pos (by group), Q_apply, mul_assoc]
  · intro b _ hb
    rw [if_neg]
    intro e; apply hb; rw [e]; group
  · intro h; exact absurd (Finset.mem_univ _) h

lemma eval_sum {ι κ : Type} [Fintype κ] (s : Finset ι) (a : ι → ℂ)
    (w : ι → EuclideanSpace ℂ κ) (g : κ) :
    (∑ h ∈ s, a h • w h) g = ∑ h ∈ s, a h * w h g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, PiLp.add_apply,
      PiLp.smul_apply, ih, smul_eq_mul]

lemma cY_conv (Y : Partition d n) (g : Equiv.Perm (Fin n)) :
    cY Y g = ∑ h, cY Y h * qY Y (h⁻¹ * g) := by
  set cv := Matrix.toEuclideanLin (youngRightOperator Y) (ket 1) with hcv
  have hmem : cv ∈ spechtSpace Y := ⟨_, rfl⟩
  have hfix := (Submodule.starProjection_eq_self_iff (K := spechtSpace Y)).mpr hmem
  have hcoord : ∀ k, cv k = cY Y k := by
    intro k
    rw [hcv, tel_apply, Finset.sum_eq_single 1]
    · simp [ket, cY]
    · intro b _ hb; simp [ket, EuclideanSpace.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hexp : cv = ∑ h, cv h • (ket h : EuclideanSpace ℂ (Equiv.Perm (Fin n))) := by
    ext k
    rw [eval_sum, Finset.sum_eq_single k]
    · simp [ket]
    · intro b _ hb; simp [ket, EuclideanSpace.single_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have := congrArg (fun v : EuclideanSpace ℂ (Equiv.Perm (Fin n)) => v g) hfix
  simp only at this
  rw [← hcoord g, ← this, hexp, map_sum]
  simp only [map_smul]
  rw [eval_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [hcoord, Pket_apply]

lemma qY_range (Y : Partition d n) :
    ∃ x : Equiv.Perm (Fin n) → ℂ, qY Y = youngRightOperator Y *ᵥ x := by
  obtain ⟨xv, hx⟩ := Submodule.starProjection_apply_mem (spechtSpace Y)
    (ket 1 : EuclideanSpace ℂ (Equiv.Perm (Fin n)))
  refine ⟨fun k => xv k, ?_⟩
  funext g
  simp only [qY]
  rw [← hx, tel_apply]
  rfl

end Proj

theorem eq17_aux (Y : Partition d n) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (piKron n ρ * isotypicProjector Y).trace =
      LinearMap.trace ℂ (schurModule Y) (polynomialRepresentation Y ρ) *
        (Module.finrank ℂ (spechtSpace Y) : ℂ) := by
  set A := piKron n ρ with hA
  set T := tensorYoungOperator Y with hT
  obtain ⟨x, hx⟩ := qY_range Y
  set X := Phi d n x with hX
  have hF : Phi d n (qY Y) = X * T := by rw [hx, Phi_R]
  have hTF : T * Phi d n (qY Y) = T := by
    rw [hT, ← Phi_cY, Phi_conv]
    congr 1
    funext g
    exact (cY_conv Y g).symm
  have hTXT : T * X * T = T := by rw [Matrix.mul_assoc, ← hF, hTF]
  have hAT : A * T = T * A := tensorYoung_comm Y ρ
  -- step 1: the character sum
  have hsum : ∑ π : Equiv.Perm (Fin n), spechtCharacter Y π⁻¹ *
      (A * tensorPermutation d n π).trace =
      (n.factorial : ℂ) * (A * Phi d n (qY Y)).trace := by
    simp only [char_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hg : ∀ g : Equiv.Perm (Fin n), ∑ π : Equiv.Perm (Fin n),
        qY Y (g⁻¹ * π * g) * (A * tensorPermutation d n π).trace =
        (A * Phi d n (qY Y)).trace := by
      intro g
      have e := Equiv.sum_comp (MulAut.conj g⁻¹).toEquiv
        (fun σ => qY Y σ * (A * tensorPermutation d n σ).trace)
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv] at e
      simp only [hA, trace_conj] at e
      rw [e, Phi, Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  -- step 2: trace of A on the Schur module
  have hE : (A * Phi d n (qY Y)).trace = (A * (T * X)).trace := by
    rw [hF, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← hAT,
      Matrix.mul_assoc]
  have hmemE : ∀ v, Matrix.toEuclideanLin (T * X) v ∈ schurModule Y := by
    intro v; rw [← lin_mul_apply]; exact LinearMap.mem_range_self _ _
  let πE : EuclideanSpace ℂ (Fin n → Fin d) →ₗ[ℂ] schurModule Y :=
    LinearMap.codRestrict (schurModule Y) (Matrix.toEuclideanLin (T * X)) hmemE
  have hlin : Matrix.toEuclideanLin (A * (T * X)) =
      (Matrix.toEuclideanLin A ∘ₗ (schurModule Y).subtype) ∘ₗ πE := by
    apply LinearMap.ext; intro v
    rw [← lin_mul_apply]; rfl
  have hres : πE ∘ₗ (Matrix.toEuclideanLin A ∘ₗ (schurModule Y).subtype) =
      polynomialRepresentation Y ρ := by
    apply LinearMap.ext; intro r
    obtain ⟨w, hw⟩ := r.2
    have hw' : Matrix.toEuclideanLin T w = r := hw
    have hm : Matrix.toEuclideanLin A r ∈ schurModule Y := by
      rw [← hw', lin_mul_apply, hAT, ← lin_mul_apply]; exact LinearMap.mem_range_self _ _
    have hmat : T * X * (A * T) = A * T := by
      rw [hAT, ← Matrix.mul_assoc, hTXT]
    apply Subtype.ext
    simp only [polynomialRepresentation, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, ContinuousLinearMap.coe_coe]
    rw [← hA]
    have h1 := congrArg Subtype.val
      ((schurModule Y).orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hm⟩)
    simp only at h1
    rw [h1]
    show Matrix.toEuclideanLin (T * X) (Matrix.toEuclideanLin A r) = Matrix.toEuclideanLin A r
    have hmat' : T * X * A * T = A * T := by rw [Matrix.mul_assoc (T * X) A T, hmat]
    rw [← hw']
    calc Matrix.toEuclideanLin (T * X) (Matrix.toEuclideanLin A (Matrix.toEuclideanLin T w))
        = Matrix.toEuclideanLin (T * X * A * T) w := by rw [lin_mul_apply, lin_mul_apply]
      _ = Matrix.toEuclideanLin (A * T) w := by rw [hmat']
      _ = Matrix.toEuclideanLin A (Matrix.toEuclideanLin T w) := by rw [lin_mul_apply]
  have htr : (A * (T * X)).trace =
      LinearMap.trace ℂ (schurModule Y) (polynomialRepresentation Y ρ) := by
    rw [← hres, ← LinearMap.trace_comp_comm', ← hlin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      Matrix.trace_toLin_eq]
  -- assemble
  have hfact : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [isotypicProjector, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [hsum, hE, htr]
  field_simp

end KW17Aux

end

open QAlgorithms QAlgorithms.Schur in
theorem solution {d N : ℕ} (Y : Partition d N) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (piKron N ρ * isotypicProjector Y).trace =
      LinearMap.trace ℂ (schurModule Y) (polynomialRepresentation Y ρ) *
        (Module.finrank ℂ (spechtSpace Y) : ℂ) := by
  exact KW17Aux.eq17_aux Y ρ
