-- Prove2me | solution 1 for LT.LatticeTree.even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/93c361d5-a5ba-57e5-9d93-706fa7ab9ca0

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow

set_option autoImplicit false

open scoped Matrix
open LT.LatticeTree

namespace TreeParity

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

private theorem algebraMap_inv_unit (w : Rˣ) :
    algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, Units.inv_mul, map_one]

private theorem exists_unit_mul_zpow_eq [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃ (w : Rˣ) (m : ℤ), x = algebraMap R K w * algebraMap R K ϖ ^ m := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨i, wa, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨j, wb, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hπK : algebraMap R K ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective R K)]; exact hϖ.ne_zero
  refine ⟨wa * wb⁻¹, (i : ℤ) - j, ?_⟩
  rw [map_mul, map_mul, map_pow, map_pow, Units.val_mul, map_mul, algebraMap_inv_unit, zpow_sub₀ hπK, zpow_natCast,
    zpow_natCast, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

private theorem zpow_exponent_eq [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) {w w' : Rˣ} {i j : ℤ}
    (h : algebraMap R K w * algebraMap R K ϖ ^ i = algebraMap R K w' * algebraMap R K ϖ ^ j) : i = j := by
  have hinj := IsFractionRing.injective R K
  have hπK : algebraMap R K ϖ ≠ 0 := by rw [map_ne_zero_iff _ hinj]; exact hϖ.ne_zero

  obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 ≤ i + N ∧ 0 ≤ j + N := ⟨(i.natAbs + j.natAbs : ℕ), by omega, by omega⟩
  have hnat : algebraMap R K ((w : R) * ϖ ^ (i + N).toNat) = algebraMap R K ((w' : R) * ϖ ^ (j + N).toNat) := by
    rw [map_mul, map_mul, map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg hN.1,
      Int.toNat_of_nonneg hN.2, zpow_add₀ hπK, zpow_add₀ hπK, ← mul_assoc, ← mul_assoc, h]
  have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ w w' _ _ (hinj hnat)
  omega

private theorem exists_pow_smul_eq_of_det_ne_zero [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (A : Matrix (Fin 2) (Fin 2) R)
    (hA : A.det ≠ 0) :
    ∃ (a : ℕ) (A₀ : Matrix (Fin 2) (Fin 2) R) (d : ℕ) (w : Rˣ),
      A = ϖ ^ a • A₀ ∧ A₀.det = w * ϖ ^ d ∧ ∃ i j, ¬ ϖ ∣ A₀ i j := by
  obtain ⟨N, wN, hN⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hA hϖ
  induction N using Nat.strong_induction_on generalizing A wN with
  | _ N ih =>
    by_cases hprim : ∃ i j, ¬ ϖ ∣ A i j
    · exact ⟨0, A, N, wN, by simp, hN, hprim⟩
    · push Not at hprim
      choose B hB using hprim
      have hAB : A = ϖ • Matrix.of B := by
        ext i j; simp [hB i j]
      have hdetB : (Matrix.of B).det ≠ 0 := by
        intro h0; apply hA; rw [hAB, Matrix.det_smul, h0, mul_zero]
      obtain ⟨N', wN', hN'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hdetB hϖ
      have hNN' : N = N' + 2 := by
        apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ wN wN'
        rw [← hN, hAB, Matrix.det_smul, hN', Fintype.card_fin]; ring
      obtain ⟨a, A₀, d, w, h1, h2, h3⟩ := ih N' (by omega) (Matrix.of B) hdetB wN' hN'
      exact ⟨a + 1, A₀, d, w, by rw [hAB, h1, smul_smul, pow_succ'], h2, h3⟩

private theorem exists_mulVec_eq_pow_smul {ϖ : R} (A₀ : Matrix (Fin 2) (Fin 2) R) {d : ℕ} {w : Rˣ}
    (hdet : A₀.det = w * ϖ ^ d) {j : ℕ} (hdj : d ≤ j) (v : Fin 2 → R) :
    ∃ t : Fin 2 → R, A₀ *ᵥ t = ϖ ^ j • v := by
  refine ⟨((w⁻¹ : Rˣ) : R) • ϖ ^ (j - d) • (A₀.adjugate *ᵥ v), ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, smul_smul]
  congr 1
  have hj : ϖ ^ j = ϖ ^ (j - d) * ϖ ^ d := by rw [← pow_add, Nat.sub_add_cancel hdj]
  have hw : ((w⁻¹ : Rˣ) : R) * w = 1 := Units.inv_mul w
  rw [hj]
  linear_combination (ϖ ^ (j - d) * ϖ ^ d) * hw

private theorem add_le_of_forall_exists_pow_smul_single_eq [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (A₀ : Matrix (Fin 2) (Fin 2) R)
    {d : ℕ} {w : Rˣ} (hdet : A₀.det = w * ϖ ^ d) {i₀ j₀ : Fin 2} (hprim : ¬ ϖ ∣ A₀ i₀ j₀) {a j : ℕ}
    (h : ∀ i : Fin 2, ∃ t : Fin 2 → R, ϖ ^ j • (Pi.single i (1 : R) : Fin 2 → R) = ϖ ^ a • (A₀ *ᵥ t)) :
    a + d ≤ j := by
  by_contra hlt
  push Not at hlt
  have hadj : ∀ r i : Fin 2, ϖ ∣ A₀.adjugate r i := by
    intro r i
    obtain ⟨t, ht⟩ := h i
    have h1 := congrArg (fun x => (A₀.adjugate *ᵥ x) r) ht
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul] at h1
    change ϖ ^ j * A₀.adjugate r i = _ at h1
    have hpow : ϖ ^ a * ϖ ^ d = ϖ ^ j * (ϖ * ϖ ^ (a + d - j - 1)) := by
      rw [← pow_succ', ← pow_add, ← pow_add]
      congr 1
      omega
    have h2 : ϖ ^ j * A₀.adjugate r i = ϖ ^ j * (ϖ * (ϖ ^ (a + d - j - 1) * ((w : R) * t r))) := by
      linear_combination h1 + ((w : R) * t r) * hpow
    exact ⟨_, mul_left_cancel₀ (pow_ne_zero j hϖ.ne_zero) h2⟩
  apply hprim
  have h00 := hadj 1 1
  have h01 := hadj 0 1
  have h10 := hadj 1 0
  have h11 := hadj 0 0
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, dvd_neg] at h00 h01 h10 h11
  fin_cases i₀ <;> fin_cases j₀ <;> assumption

section FieldSide

private theorem exists_algebraMap_eq_zpow (w : Rˣ) (m : ℤ) :
    ∃ w₁ : Rˣ, algebraMap R K (w : R) ^ m = algebraMap R K (w₁ : R) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact ⟨w ^ n, by rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]⟩
  · refine ⟨w⁻¹ ^ n, ?_⟩
    rw [zpow_neg, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, algebraMap_inv_unit, inv_pow]

private theorem exists_toField_eq [IsDomain R] [IsDiscreteValuationRing R]
    (σ : IntegralAut R K) {ϖ : R} (hϖ : Irreducible ϖ) (w : Rˣ) (m : ℤ) :
    ∃ w' : Rˣ, σ.toField (algebraMap R K (w : R) * algebraMap R K ϖ ^ m) =
      algebraMap R K (w' : R) * algebraMap R K ϖ ^ m := by
  have hirr : Irreducible (σ.toBase ϖ) := (MulEquiv.irreducible_iff σ.toBase).mpr hϖ
  obtain ⟨w₀, hw₀⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hirr
  obtain ⟨w₁, hw₁⟩ := exists_algebraMap_eq_zpow (K := K) w₀ m
  obtain ⟨W, hW⟩ : ∃ W : Rˣ, (W : R) = σ.toBase w := ⟨Units.map σ.toBase.toRingHom.toMonoidHom w, rfl⟩
  refine ⟨W * w₁, ?_⟩
  rw [map_mul, map_zpow₀, σ.commutes, σ.commutes, ← hw₀, map_mul, mul_zpow, hw₁, Units.val_mul, map_mul, hW]
  ring

private theorem isInteger_of_latticeMap_le {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : latticeMap γ (stdLattice R K) ≤ stdLattice R K) (i j : Fin 2) :
    IsLocalization.IsInteger R ((γ : Matrix (Fin 2) (Fin 2) K) i j) := by
  have hmem := hγ (mulVec_mem_latticeMap (g := γ) (single_one_mem_stdLattice R K j))
  rw [mulVec_single_one] at hmem
  exact (mem_stdLattice R K).mp hmem i

private theorem exists_map_eq (γ : Matrix (Fin 2) (Fin 2) K) (hγ : ∀ i j, IsLocalization.IsInteger R (γ i j)) :
    ∃ A : Matrix (Fin 2) (Fin 2) R, A.map (algebraMap R K) = γ := by
  have h' : ∀ i j, ∃ y : R, algebraMap R K y = γ i j := fun i j => hγ i j
  choose A hA using h'
  exact ⟨Matrix.of A, by ext i j; simp [hA i j]⟩

private theorem exists_comp_eq {v : Fin 2 → K} (hv : v ∈ stdLattice R K) :
    ∃ t : Fin 2 → R, (fun i => algebraMap R K (t i)) = v := by
  have h' : ∀ i, ∃ y : R, algebraMap R K y = v i := fun i => (mem_stdLattice R K).mp hv i
  choose t ht using h'
  exact ⟨t, funext ht⟩

private theorem comp_mem (t : Fin 2 → R) : (fun i => algebraMap R K (t i)) ∈ stdLattice R K :=
  (mem_stdLattice R K).mpr fun i => ⟨t i, rfl⟩

private theorem map_mulVec_comp (A : Matrix (Fin 2) (Fin 2) R) (t : Fin 2 → R) :
    A.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (t i)) = fun i => algebraMap R K ((A *ᵥ t) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul]

private theorem exists_gl_coe_eq [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : ϖ ≠ 0) (A₀ : Matrix (Fin 2) (Fin 2) R) {d : ℕ} {w : Rˣ}
    (hdet : A₀.det = w * ϖ ^ d) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ₀ : Matrix (Fin 2) (Fin 2) K) = A₀.map (algebraMap R K) := by
  have hne : (A₀.map (algebraMap R K)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact mul_ne_zero w.ne_zero (pow_ne_zero _ hϖ)
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, rfl⟩

private theorem add_le_of_latticeMap_le [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {γ' : Matrix.GeneralLinearGroup (Fin 2) K}
    {A₀ : Matrix (Fin 2) (Fin 2) R} {a : ℕ}
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ ^ a • A₀.map (algebraMap R K)) {d : ℕ} {w : Rˣ}
    (hdet : A₀.det = w * ϖ ^ d) {i₀ j₀ : Fin 2} (hprim : ¬ ϖ ∣ A₀ i₀ j₀) {j : ℕ}
    (hle : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ j)) (stdLattice R K) ≤
      latticeMap γ' (stdLattice R K)) : a + d ≤ j := by
  refine add_le_of_forall_exists_pow_smul_single_eq hϖ A₀ hdet hprim fun i => ?_
  have hmem : ((unitOfNeZero (K := K) hϖ.ne_zero ^ j : Kˣ) : K) • (Pi.single i (1 : K) : Fin 2 → K) ∈
      latticeMap γ' (stdLattice R K) :=
    hle (mem_latticeMap_scalarGL.mpr ⟨_, single_one_mem_stdLattice R K i, rfl⟩)
  obtain ⟨y, hy, hyv⟩ := mem_latticeMap.mp hmem
  obtain ⟨t, rfl⟩ := exists_comp_eq hy
  refine ⟨t, funext fun r => IsFractionRing.injective R K ?_⟩
  have hr := congrFun hyv r
  rw [hγ', Matrix.smul_mulVec, map_mulVec_comp, Units.val_pow_eq_pow_val, unitOfNeZero_coe] at hr
  simp only [Pi.smul_apply, smul_eq_mul] at hr
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, map_pow, map_pow, hr]
  by_cases hri : r = i
  · subst hri; simp
  · simp [hri]

private theorem latticeWithin_of_le [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {γ₀ : Matrix.GeneralLinearGroup (Fin 2) K}
    {A₀ : Matrix (Fin 2) (Fin 2) R} (hγ₀ : (γ₀ : Matrix (Fin 2) (Fin 2) K) = A₀.map (algebraMap R K)) {d : ℕ}
    {w : Rˣ} (hdet : A₀.det = w * ϖ ^ d) {j : ℕ} (hdj : d ≤ j) :
    LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) j (stdLattice R K) (latticeMap γ₀ (stdLattice R K)) := by
  constructor
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    obtain ⟨s, rfl⟩ := exists_comp_eq hy
    obtain ⟨t, ht⟩ := exists_mulVec_eq_pow_smul A₀ hdet hdj s
    refine mem_latticeMap.mpr ⟨fun i => algebraMap R K (t i), comp_mem t, ?_⟩
    rw [hγ₀, map_mulVec_comp, ht, Units.val_pow_eq_pow_val, unitOfNeZero_coe]
    funext r
    simp [map_pow]
  · refine latticeMap_le_stdLattice_of_isInteger fun i j => ?_
    rw [hγ₀]
    exact ⟨A₀ i j, by simp⟩

private theorem homothetic_of_coe_eq [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {γ' γ₀ : Matrix.GeneralLinearGroup (Fin 2) K}
    {a : ℕ} (h : (γ' : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ ^ a • (γ₀ : Matrix (Fin 2) (Fin 2) K))
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ a)) (latticeMap γ₀ L) = latticeMap γ' L := by
  rw [← latticeMap_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, scalarGL_coe, h, Matrix.smul_mul, Matrix.one_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe]

end FieldSide

section Core

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
include hϖ

private theorem exists_det_inv_mul_det_eq (h h' : Matrix.GeneralLinearGroup (Fin 2) K) (n : ℕ)
    (H1 : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) (Vertex.act h (stdVertex R K))
      (Vertex.act h' (stdVertex R K)))
    (H0 : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (Vertex.act h (stdVertex R K))
      (Vertex.act h' (stdVertex R K))) :
    ∃ (w : Rˣ) (m : ℤ), ((h : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * (h' : Matrix (Fin 2) (Fin 2) K).det =
      algebraMap R K (w : R) * algebraMap R K ϖ ^ ((n : ℤ) + 1 + 2 * m) := by
  obtain ⟨L, M, hL, hM, hLx, hMy, hLM⟩ := H1

  have hLx' : Vertex.mk R K L hL = Vertex.mk R K (latticeMap h (stdLattice R K)) (isFullLattice_stdLattice.map h) :=
    hLx
  have hMy' : Vertex.mk R K M hM =
      Vertex.mk R K (latticeMap h' (stdLattice R K)) (isFullLattice_stdLattice.map h') := hMy
  obtain ⟨e, he⟩ := (Vertex.mk_eq_mk_iff.mp hLx').symm
  obtain ⟨f, hf⟩ := (Vertex.mk_eq_mk_iff.mp hMy').symm
  rw [← latticeMap_mul] at he hf
  set gL := scalarGL e * h with hgL
  set gM := scalarGL f * h' with hgM
  set γ' := gL⁻¹ * gM with hγ'def
  have hMeq : M = latticeMap gL (latticeMap γ' (stdLattice R K)) := by
    rw [← latticeMap_mul, hγ'def, mul_inv_cancel_left, hf]
  have hsand : LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) (stdLattice R K)
      (latticeMap γ' (stdLattice R K)) := by
    rw [← he, hMeq] at hLM
    exact (latticeWithin_latticeMap_iff _ _ _ _ _).mp hLM
  obtain ⟨hlow, hup⟩ := hsand

  obtain ⟨A, hA⟩ := exists_map_eq _ (isInteger_of_latticeMap_le hup)
  have hAdet : A.det ≠ 0 := by
    intro h0
    have hdet0 : ((γ' : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
      rw [← hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    exact Matrix.GeneralLinearGroup.det_ne_zero γ' hdet0
  obtain ⟨a, A₀, d, w, hAsplit, hA₀det, i₀, j₀, hprim⟩ := exists_pow_smul_eq_of_det_ne_zero hϖ A hAdet
  obtain ⟨γ₀, hγ₀⟩ := exists_gl_coe_eq (K := K) hϖ.ne_zero A₀ hA₀det
  have hγ'coe : (γ' : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ ^ a • A₀.map (algebraMap R K) := by
    rw [← hA, hAsplit]
    ext i j
    simp [Matrix.map_apply, map_mul, map_pow]
  have hγ'γ₀ : (γ' : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ ^ a • (γ₀ : Matrix (Fin 2) (Fin 2) K) := by
    rw [hγ'coe, hγ₀]

  have hupper : a + d ≤ n + 1 := add_le_of_latticeMap_le hϖ hγ'coe hA₀det hprim hlow
  have hlower : n + 1 ≤ d := by
    by_contra hlt
    apply H0
    have hW := latticeWithin_of_le hϖ hγ₀ hA₀det (j := n) (by omega)
    refine ⟨L, latticeMap gL (latticeMap γ₀ (stdLattice R K)), hL,
      (isFullLattice_stdLattice.map γ₀).map gL, hLx, ?_, ?_⟩
    · rw [← hMy]
      refine Vertex.mk_eq_mk_iff.mpr ⟨unitOfNeZero (K := K) hϖ.ne_zero ^ a, ?_⟩
      rw [hMeq, ← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul, homothetic_of_coe_eq hϖ hγ'γ₀]
    · rw [← he]
      exact (latticeWithin_latticeMap_iff _ _ _ _ _).mpr hW
  have ha : a = 0 := by omega
  have hd : d = n + 1 := by omega
  subst ha hd

  have hγ'det : (γ' : Matrix (Fin 2) (Fin 2) K).det =
      algebraMap R K (w : R) * algebraMap R K ϖ ^ (n + 1) := by
    rw [hγ'coe, pow_zero, one_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hA₀det, map_mul, map_pow]
  have hγ'det' : (γ' : Matrix (Fin 2) (Fin 2) K).det =
      ((gL : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * (gM : Matrix (Fin 2) (Fin 2) K).det := by
    rw [hγ'def, Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hgLdet : (gL : Matrix (Fin 2) (Fin 2) K).det = (e : K) ^ 2 * (h : Matrix (Fin 2) (Fin 2) K).det := by
    rw [hgL, Units.val_mul, Matrix.det_mul, scalarGL_coe, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hgMdet : (gM : Matrix (Fin 2) (Fin 2) K).det = (f : K) ^ 2 * (h' : Matrix (Fin 2) (Fin 2) K).det := by
    rw [hgM, Units.val_mul, Matrix.det_mul, scalarGL_coe, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hhdet : (h : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero h
  have hef : ((e : K) / f) ≠ 0 := div_ne_zero e.ne_zero f.ne_zero
  obtain ⟨w₂, m, hw₂⟩ := exists_unit_mul_zpow_eq (K := K) hϖ hef
  refine ⟨w₂ ^ 2 * w, m, ?_⟩
  have hquot : ((h : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * (h' : Matrix (Fin 2) (Fin 2) K).det =
      ((e : K) / f) ^ 2 * (γ' : Matrix (Fin 2) (Fin 2) K).det := by
    rw [hγ'det', hgLdet, hgMdet]
    field_simp
  have hπK : algebraMap R K ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective R K)]; exact hϖ.ne_zero
  rw [hquot, hw₂, hγ'det, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, zpow_add₀ hπK,
    zpow_add₀ hπK, zpow_one, zpow_natCast, mul_comm (2 : ℤ) m, zpow_mul, zpow_two]
  ring

end Core

section Heads

private theorem twistedAct_act_stdVertex (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (h : Matrix.GeneralLinearGroup (Fin 2) K) :
    Vertex.twistedAct δ σ (Vertex.act h (stdVertex R K)) = Vertex.act (δ * σ.mapGL h) (stdVertex R K) := by
  simp only [Vertex.twistedAct, stdVertex, Vertex.act_mk, Vertex.galAct_mk]
  exact Vertex.mk_eq_mk_iff.mpr ⟨1, by
    rw [scalarGL_one, latticeMap_one, latticeGal_latticeMap, latticeGal_stdLattice, latticeMap_mul]⟩

private theorem det_mapGL (σ : IntegralAut R K) (h : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((σ.mapGL h : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      σ.toField (h : Matrix (Fin 2) (Fin 2) K).det := by
  rw [IntegralAut.mapGL_coe, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

private theorem exists_det_inv_mul_det_twisted_eq [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (σ : IntegralAut R K)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {k : ℤ} {u : Rˣ}
    (hdet : (δ : Matrix (Fin 2) (Fin 2) K).det = algebraMap R K u * algebraMap R K ϖ ^ k)
    (h : Matrix.GeneralLinearGroup (Fin 2) K) :
    ∃ w : Rˣ, ((h : Matrix (Fin 2) (Fin 2) K).det)⁻¹ *
        ((δ * σ.mapGL h : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      algebraMap R K (w : R) * algebraMap R K ϖ ^ k := by
  have hhdet : (h : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero h
  obtain ⟨wh, mh, hwh⟩ := exists_unit_mul_zpow_eq (K := K) hϖ hhdet
  obtain ⟨wh', hwh'⟩ := exists_toField_eq σ hϖ wh mh
  have hπK : algebraMap R K ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective R K)]; exact hϖ.ne_zero
  have hwhK : algebraMap R K (wh : R) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective R K)]; exact wh.ne_zero
  refine ⟨wh⁻¹ * (u * wh'), ?_⟩
  rw [Units.val_mul, Matrix.det_mul, det_mapGL, hwh, hwh', hdet, Units.val_mul, Units.val_mul, map_mul, map_mul,
    algebraMap_inv_unit]
  field_simp

private theorem parity_twisted [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (ϖ : R) (hϖ : Irreducible ϖ)
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = v)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (k : ℤ) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (∀ x : Vertex R K, x ∈ twistedFixedVertexSet δ σ → Even k) ∧
    ∀ (n : ℕ) (x : Vertex R K),
      x ∈ twistedOrbitalBall (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) δ σ \
          twistedOrbitalBall (unitOfNeZero (K := K) hϖ.ne_zero) (n) δ σ →
      Even ((n : ℤ) + 1 - k) := by
  refine ⟨fun x hx => ?_, fun n x hx => ?_⟩
  · obtain ⟨h, rfl⟩ := htrans x
    rw [mem_twistedFixedVertexSet, twistedAct_act_stdVertex] at hx
    have hstd : Vertex.act (h⁻¹ * (δ * σ.mapGL h)) (stdVertex R K) = stdVertex R K := by
      rw [Vertex.act_mul, hx, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]
    obtain ⟨c₀, r, hr⟩ := (Vertex.act_stdVertex_eq_iff _).mp hstd

    have hrcoe : ((Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) r :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (r : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := by
      ext i j
      exact Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j r
    have hrdet : ((Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) r :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
        algebraMap R K ((Matrix.GeneralLinearGroup.det r : Rˣ) : R) * algebraMap R K ϖ ^ (0 : ℤ) := by
      have hval : ((Matrix.GeneralLinearGroup.det r : Rˣ) : R) = (r : Matrix (Fin 2) (Fin 2) R).det := rfl
      rw [hrcoe, ← RingHom.mapMatrix_apply, ← RingHom.map_det, zpow_zero, mul_one, hval]
    have hinvdet : ((h⁻¹ * (δ * σ.mapGL h) : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).det =
        ((h : Matrix (Fin 2) (Fin 2) K).det)⁻¹ *
          ((δ * σ.mapGL h : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
      rw [Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    obtain ⟨w₁, hw₁⟩ := exists_det_inv_mul_det_twisted_eq hϖ σ δ hdet h
    obtain ⟨wc, mc, hwc⟩ := exists_unit_mul_zpow_eq (K := K) hϖ c₀.ne_zero
    have hπK : algebraMap R K ϖ ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective R K)]; exact hϖ.ne_zero
    have hfinal : algebraMap R K ((wc ^ 2 * w₁ : Rˣ) : R) * algebraMap R K ϖ ^ (2 * mc + k) =
        algebraMap R K ((Matrix.GeneralLinearGroup.det r : Rˣ) : R) * algebraMap R K ϖ ^ (0 : ℤ) := by
      rw [← hrdet, hr, Units.val_mul (scalarGL c₀), Matrix.det_mul, scalarGL_coe, Matrix.det_smul, Matrix.det_one,
        Fintype.card_fin, mul_one, hinvdet, hw₁, hwc, Units.val_mul (wc ^ 2), Units.val_pow_eq_pow_val, map_mul,
        map_pow, zpow_add₀ hπK, mul_comm (2 : ℤ) mc, zpow_mul, zpow_two]
      ring
    have := zpow_exponent_eq hϖ hfinal
    exact ⟨-mc, by omega⟩
  · rw [Set.mem_diff, mem_twistedOrbitalBall, mem_twistedOrbitalBall] at hx
    obtain ⟨h, rfl⟩ := htrans x
    rw [twistedAct_act_stdVertex] at hx
    obtain ⟨H1, H0⟩ := hx
    obtain ⟨w, m, hwm⟩ := exists_det_inv_mul_det_eq hϖ h (δ * σ.mapGL h) n H1 H0
    obtain ⟨w₁, hw₁⟩ := exists_det_inv_mul_det_twisted_eq hϖ σ δ hdet h
    have := zpow_exponent_eq hϖ (hw₁.symm.trans hwm)
    exact ⟨-m, by omega⟩

end Heads

end TreeParity

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (k : ℤ) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (∀ x : LT.LatticeTree.Vertex R K, x ∈ LT.LatticeTree.twistedFixedVertexSet δ σ → Even k) ∧
    ∀ (n : ℕ) (x : LT.LatticeTree.Vertex R K),
      x ∈
        LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n) δ σ →
      Even ((n : ℤ) + 1 - k) := by
  exact TreeParity.parity_twisted ϖ hϖ (fun v => LT.LatticeTree.exists_act_stdVertex_eq R K v) σ δ k u hdet

#print axioms solution

end S_LT_LatticeTree_even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow
end P2MW
export P2MW.S_LT_LatticeTree_even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow (solution)
