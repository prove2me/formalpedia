-- Prove2me | solution 1 for ModernConvex.Relaxations.nesterov_ye
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T23:19:03.802493+00:00
-- url     : https://prove2.me/submissions/97484e56-cc7e-4511-b7f2-06c93926be01

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_QuadraticSystem
import Theorems.Thm_ModernConvex_Relaxations_nesterov_theorem
import Theorems.Thm_VBSDP_Duality_theorem_3_1

open Matrix
open ModernConvex.Relaxations

namespace NY99


theorem ny_eig {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i).IsHermitian)
    (hcomm : ∀ i j, B i * B j = B j * B i) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      ∀ i, ∃ b : Fin n → ℝ, Uᵀ * B i * U = diagonal b := by
  classical
  let T : Fin m → Module.End ℝ (EuclideanSpace ℝ (Fin n)) := fun i => toEuclideanLin (B i)
  have hT : ∀ i, (T i).IsSymmetric := fun i => isSymmetric_toEuclideanLin_iff.mpr (hB i)
  have hC : Pairwise (Function.onFun Commute T) := by
    intro i j _
    show T i * T j = T j * T i
    apply LinearMap.ext; intro x
    simp only [T, Module.End.mul_apply, toLpLin_apply, mulVec_mulVec,
      hcomm i j]
  have hV := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hC
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  let V : (Fin m → ℝ) → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun α => ⨅ j, Module.End.eigenspace (T j) (α j)
  let _ : Fintype {α // V α ≠ ⊥} := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hW : DirectSum.IsInternal (fun α : {α // V α ≠ ⊥} => V α) :=
    DirectSum.isInternal_ne_bot_iff.mpr hV
  have hW' : OrthogonalFamily ℝ (fun α : {α // V α ≠ ⊥} => V α) fun α => (V α).subtypeₗᵢ :=
    hV'.comp Subtype.val_injective
  let v := hW.subordinateOrthonormalBasis hn hW'
  let γ := fun k => (hW.subordinateOrthonormalBasisIndex hn k hW').1
  have hv : ∀ k i, B i *ᵥ (v k).ofLp = γ k i • (v k).ofLp := by
    intro k i
    have h1 := hW.subordinateOrthonormalBasis_subordinate hn k hW'
    simp only [V] at h1
    rw [Submodule.mem_iInf] at h1
    have h2 := Module.End.mem_eigenspace_iff.mp (h1 i)
    have h3 := congrArg WithLp.ofLp h2
    simpa [T, toLpLin_apply] using h3
  let U : Matrix (Fin n) (Fin n) ℝ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix v
  have hU : ∀ r k, U r k = v k r := by
    intro r k; simp [U, Module.Basis.toMatrix_apply]
  have hmem := (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_unitary v
  have h1 : Uᵀ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hmem
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  have h2 : U * Uᵀ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hmem
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  refine ⟨U, h1, h2, fun i => ⟨fun k => γ k i, ?_⟩⟩
  have hBU : B i * U = U * diagonal (fun k => γ k i) := by
    ext r k
    rw [mul_diagonal, hU]
    have := congrFun (hv k i) r
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [mul_comm, ← this, Matrix.mul_apply, mulVec, dotProduct]
    simp [hU]
  rw [Matrix.mul_assoc, hBU, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end NY99


open Matrix
open ModernConvex.Relaxations

namespace NY99

/-- For a real PSD matrix, `X j k ^ 2 ≤ X j j * X k k`. -/
theorem rndR_entry_sq {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (j k : Fin n) :
    X j k ^ 2 ≤ X j j * X k k := by
  by_cases hjk : j = k
  · subst hjk; nlinarith
  have hsym : X k j = X j k := by
    have := hX.1.apply j k
    simpa using this
  have h : ∀ t : ℝ, 0 ≤ X j j * (t * t) + (-2 * X j k) * t + X k k := by
    intro t
    have := hX.dotProduct_mulVec_nonneg (t • Pi.single j 1 - Pi.single k 1)
    simp only [star_trivial, mulVec_sub, mulVec_smul, mulVec_single_one, sub_dotProduct,
      dotProduct_sub, smul_dotProduct, dotProduct_smul, single_dotProduct, smul_eq_mul] at this
    simp only [col_apply, one_mul] at this
    rw [hsym] at this
    nlinarith [this]
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith [this]

theorem rndR_quad {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((Pᵀ * N * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (N *ᵥ (P *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem rndR_tr {n : ℕ} (M P Y : Matrix (Fin n) (Fin n) ℝ) :
    (M * (P * Y * Pᵀ)).trace = (Pᵀ * M * P * Y).trace := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem ny_round_of_eig {n m : ℕ} (S : QuadraticSystem n m)
    (hU : ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      ∀ i, ∃ b : Fin n → ℝ, Uᵀ * S.B i * U = diagonal b)
    (hA : S.A.PosSemidef) (fstar : ℝ) (hf : S.IsPValue fstar)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : S.SDPFeasible X) :
    2 / Real.pi * (S.A * X).trace ≤ fstar := by
  obtain ⟨U, _hUU, hUU', hb⟩ := hU
  choose b hb using hb
  set X' : Matrix (Fin n) (Fin n) ℝ := Uᵀ * X * U with hX'def
  have hX' : X'.PosSemidef := by
    simpa using hX.2.conjTranspose_mul_mul_same U
  set s : Fin n → ℝ := fun j => X' j j with hsdef
  have hs : ∀ j, 0 ≤ s j := fun j => hX'.diag_nonneg
  set d : Fin n → ℝ := fun j => Real.sqrt (s j) with hddef
  set D : Matrix (Fin n) (Fin n) ℝ := diagonal d with hDdef
  set e : Fin n → ℝ := fun j => if s j = 0 then 0 else 1 / Real.sqrt (s j) with hedef
  set E : Matrix (Fin n) (Fin n) ℝ := diagonal e with hEdef
  set z : Fin n → ℝ := fun j => if s j = 0 then 1 else 0 with hzdef
  set C : Matrix (Fin n) (Fin n) ℝ := E * X' * E + diagonal z with hCdef
  have hC : C.PosSemidef := by
    refine PosSemidef.add ?_ ?_
    · have := hX'.conjTranspose_mul_mul_same E
      simpa [hEdef] using this
    · rw [posSemidef_diagonal_iff]
      intro j; simp only [hzdef]; split_ifs <;> norm_num
  have hCe : ∀ j k, C j k = e j * X' j k * e k + diagonal z j k := by
    intro j k
    simp [hCdef, hEdef, diagonal_mul, mul_diagonal]
  have hCdiag : ∀ j, C j j = 1 := by
    intro j
    rw [hCe]
    simp only [diagonal_apply_eq, hzdef, hedef]
    by_cases h0 : s j = 0
    · simp [h0]
    · simp only [h0, if_false, add_zero]
      have hpos : 0 < s j := lt_of_le_of_ne (hs j) (Ne.symm h0)
      have hsq := Real.sq_sqrt (hs j)
      have hne : Real.sqrt (s j) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      change 1 / Real.sqrt (s j) * s j * (1 / Real.sqrt (s j)) = 1
      field_simp
      nlinarith [hsq]
  have hzero : ∀ j k, s j = 0 → X' j k = 0 := by
    intro j k h0
    have := rndR_entry_sq hX' j k
    have h' : X' j j = 0 := h0
    rw [h', zero_mul] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
  have hzero' : ∀ j k, s k = 0 → X' j k = 0 := by
    intro j k h0
    have hsym : X' j k = X' k j := by
      have := hX'.1.apply k j
      simpa using this
    rw [hsym]; exact hzero k j h0
  have hde : ∀ j, s j ≠ 0 → d j * e j = 1 := by
    intro j h0
    have hpos : 0 < s j := lt_of_le_of_ne (hs j) (Ne.symm h0)
    have hne : Real.sqrt (s j) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    simp only [hddef, hedef, h0, if_false]
    field_simp
  have hDCD : D * C * D = X' := by
    ext j k
    simp only [hDdef, diagonal_mul, mul_diagonal]
    rw [hCe]
    by_cases hj : s j = 0
    · have : d j = 0 := by simp [hddef, hj]
      rw [this, hzero j k hj]; ring
    by_cases hk : s k = 0
    · have : d k = 0 := by simp [hddef, hk]
      rw [this, hzero' j k hk]; ring
    have hz : diagonal z j k = 0 := by
      by_cases hjk : j = k
      · subst hjk; simp [hzdef, hj]
      · simp [diagonal_apply_ne _ hjk]
    rw [hz, add_zero]
    calc d j * (e j * X' j k * e k) * d k = (d j * e j) * X' j k * (d k * e k) := by ring
      _ = X' j k := by rw [hde j hj, hde k hk]; ring
  have hXeq : X = (U * D) * C * (U * D)ᵀ := by
    rw [transpose_mul, hDdef, diagonal_transpose, ← hDdef]
    have : U * D * C * (D * Uᵀ) = U * (D * C * D) * Uᵀ := by
      simp only [Matrix.mul_assoc]
    rw [this, hDCD, hX'def]
    calc X = (U * Uᵀ) * X * (U * Uᵀ) := by rw [hUU']; simp
      _ = U * (Uᵀ * X * U) * Uᵀ := by simp only [Matrix.mul_assoc]
  set A'' : Matrix (Fin n) (Fin n) ℝ := (U * D)ᵀ * S.A * (U * D) with hA''def
  have hA'' : A''.PosSemidef := by
    have := hA.conjTranspose_mul_mul_same (U * D)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have htr : (S.A * X).trace = (A'' * C).trace := by
    rw [hXeq, rndR_tr]
  -- the sign-vector bound
  have hsign : ∀ x : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) → x ⬝ᵥ (A'' *ᵥ x) ≤ fstar := by
    intro x hx
    have hy : S.Solves ((U * D) *ᵥ x) := by
      intro i
      rw [← rndR_quad]
      have hBD : (U * D)ᵀ * S.B i * (U * D) = diagonal (fun j => d j * b i j * d j) := by
        rw [transpose_mul, hDdef, diagonal_transpose]
        have : diagonal d * Uᵀ * S.B i * (U * diagonal d)
            = diagonal d * (Uᵀ * S.B i * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
        rw [this, hb i, diagonal_mul_diagonal, diagonal_mul_diagonal]
      rw [hBD]
      have hval : x ⬝ᵥ (diagonal (fun j => d j * b i j * d j) *ᵥ x) = ∑ j, b i j * s j := by
        simp only [dotProduct, mulVec_diagonal]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hdd : d j * d j = s j := Real.mul_self_sqrt (hs j)
        have hxx : x j * x j = 1 := by rcases hx j with h | h <;> rw [h] <;> norm_num
        calc x j * (d j * b i j * d j * x j) = b i j * (d j * d j) * (x j * x j) := by ring
          _ = b i j * s j := by rw [hdd, hxx, mul_one]
      rw [hval]
      have htrB : (S.B i * X).trace = ∑ j, b i j * s j := by
        have : X = U * X' * Uᵀ := by
          rw [hX'def]
          calc X = (U * Uᵀ) * X * (U * Uᵀ) := by rw [hUU']; simp
            _ = U * (Uᵀ * X * U) * Uᵀ := by simp only [Matrix.mul_assoc]
        rw [this, rndR_tr, hb i]
        simp [trace, diagonal_mul, hsdef]
      rw [← htrB]
      exact hX.1 i
    have := hf.1 ⟨(U * D) *ᵥ x, hy, rfl⟩
    rw [hA''def, rndR_quad]
    exact this
  -- OPT
  set Sopt := ((fun x : Fin n → ℝ => x ⬝ᵥ (A'' *ᵥ x)) '' {x | ∀ i, x i = 1 ∨ x i = -1})
    with hSopt
  have hSopt_ne : Sopt.Nonempty := ⟨_, ⟨fun _ => 1, fun _ => Or.inl rfl, rfl⟩⟩
  have hSopt_bdd : fstar ∈ upperBounds Sopt := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsign x hx
  have hOPT : IsLUB Sopt (sSup Sopt) := isLUB_csSup hSopt_ne ⟨fstar, hSopt_bdd⟩
  have hOPTle : sSup Sopt ≤ fstar := csSup_le hSopt_ne hSopt_bdd
  -- SDP
  set Ssdp := ((fun X : Matrix (Fin n) (Fin n) ℝ => (A'' * X).trace) ''
      {X | X.PosSemidef ∧ ∀ i, X i i = 1}) with hSsdp
  have hSsdp_ne : Ssdp.Nonempty := ⟨_, ⟨1, ⟨PosSemidef.one, fun i => by simp⟩, rfl⟩⟩
  have hSsdp_bdd : (∑ j, ∑ k, |A'' j k|) ∈ upperBounds Ssdp := by
    rintro _ ⟨Y, ⟨hY, hY1⟩, rfl⟩
    simp only [trace, diag_apply, mul_apply]
    refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
    have hle : |Y k j| ≤ 1 := by
      have h1 := rndR_entry_sq hY k j
      rw [hY1, hY1, mul_one] at h1
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    calc A'' j k * Y k j ≤ |A'' j k * Y k j| := le_abs_self _
      _ = |A'' j k| * |Y k j| := abs_mul _ _
      _ ≤ |A'' j k| * 1 := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = |A'' j k| := mul_one _
  have hSDP : IsLUB Ssdp (sSup Ssdp) := isLUB_csSup hSsdp_ne ⟨_, hSsdp_bdd⟩
  have hCle : (A'' * C).trace ≤ sSup Ssdp :=
    le_csSup ⟨_, hSsdp_bdd⟩ ⟨C, ⟨hC, hCdiag⟩, rfl⟩
  have hnest := (nesterov_theorem A'' hA'' (sSup Sopt) (sSup Ssdp) hOPT hSDP).2
  have hpi : 0 ≤ 2 / Real.pi := by positivity
  rw [htr]
  calc 2 / Real.pi * (A'' * C).trace ≤ 2 / Real.pi * sSup Ssdp :=
        mul_le_mul_of_nonneg_left hCle hpi
    _ ≤ sSup Sopt := hnest
    _ ≤ fstar := hOPTle

end NY99


open Matrix
open ModernConvex.Relaxations

namespace NY99

/-- block diagonal matrix with blocks of sizes `n` and `m` -/
def sddD_bd {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (n+m)) (Fin (n+m)) ℝ :=
  fun a b => Fin.addCases (fun i => Fin.addCases (fun j => M i j) (fun _ => (0:ℝ)) b)
    (fun i => Fin.addCases (fun _ => (0:ℝ)) (fun j => W i j) b) a

section
variable {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
lemma sddD_bd_ll (i j : Fin n) : sddD_bd M W (Fin.castAdd m i) (Fin.castAdd m j) = M i j := by
  simp [sddD_bd]
lemma sddD_bd_lr (i : Fin n) (j : Fin m) : sddD_bd M W (Fin.castAdd m i) (Fin.natAdd n j) = 0 := by
  simp [sddD_bd, -Fin.natAdd_eq_addNat]
lemma sddD_bd_rl (i : Fin m) (j : Fin n) : sddD_bd M W (Fin.natAdd n i) (Fin.castAdd m j) = 0 := by
  simp [sddD_bd, -Fin.natAdd_eq_addNat]
lemma sddD_bd_rr (i j : Fin m) : sddD_bd M W (Fin.natAdd n i) (Fin.natAdd n j) = W i j := by
  simp [sddD_bd, -Fin.natAdd_eq_addNat]
end

lemma sddD_bd_quad {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin (n+m) → ℝ) :
    x ⬝ᵥ (sddD_bd M W *ᵥ x) = (fun i => x (Fin.castAdd m i)) ⬝ᵥ (M *ᵥ fun i => x (Fin.castAdd m i))
      + (fun i => x (Fin.natAdd n i)) ⬝ᵥ (W *ᵥ fun i => x (Fin.natAdd n i)) := by
  simp [dotProduct, mulVec, Fin.sum_univ_add, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr,
    -Fin.natAdd_eq_addNat]

lemma sddD_bd_herm {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.IsHermitian) (hW : W.IsHermitian) : (sddD_bd M W).IsHermitian := by
  have hM' : ∀ a b, M a b = M b a := fun a b => by simpa using (hM.apply b a)
  have hW' : ∀ a b, W a b = W b a := fun a b => by simpa using (hW.apply b a)
  ext a b
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp [hM', hW', -Fin.natAdd_eq_addNat, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr]

lemma sddD_bd_psd {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.PosSemidef) (hW : W.PosSemidef) : (sddD_bd M W).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨sddD_bd_herm hM.isHermitian hW.isHermitian, fun x => ?_⟩
  simp only [star_trivial, sddD_bd_quad]
  have h1 := hM.dotProduct_mulVec_nonneg (fun i => x (Fin.castAdd m i))
  have h2 := hW.dotProduct_mulVec_nonneg (fun i => x (Fin.natAdd n i))
  simp only [star_trivial] at h1 h2
  linarith

lemma sddD_bd_posDef {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.PosDef) (hW : W.PosDef) : (sddD_bd M W).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨sddD_bd_herm hM.isHermitian hW.isHermitian, fun x hx => ?_⟩
  simp only [star_trivial, sddD_bd_quad]
  have h1 := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => x (Fin.castAdd m i))
  have h2 := hW.posSemidef.dotProduct_mulVec_nonneg (fun i => x (Fin.natAdd n i))
  simp only [star_trivial] at h1 h2
  by_cases hu : (fun i => x (Fin.castAdd m i)) = 0
  · have hv : (fun i => x (Fin.natAdd n i)) ≠ 0 := by
      intro hv
      apply hx
      ext a
      induction a using Fin.addCases with
      | left i => exact congrFun hu i
      | right i => exact congrFun hv i
    have := hW.dotProduct_mulVec_pos hv
    simp only [star_trivial] at this
    linarith
  · have := hM.dotProduct_mulVec_pos hu
    simp only [star_trivial] at this
    linarith

lemma sddD_bd_psd_left {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (h : (sddD_bd M W).PosSemidef) : M.PosSemidef := by
  have := h.submatrix (Fin.castAdd m)
  convert this using 1
  ext i j; simp [sddD_bd_ll]

lemma sddD_bd_psd_right {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (h : (sddD_bd M W).PosSemidef) : W.PosSemidef := by
  have := h.submatrix (Fin.natAdd n)
  convert this using 1
  ext i j; simp [sddD_bd_rr, -Fin.natAdd_eq_addNat]

lemma sddD_bd_trace {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ) :
    (sddD_bd M W * Z).trace = (M * Z.submatrix (Fin.castAdd m) (Fin.castAdd m)).trace
      + (W * Z.submatrix (Fin.natAdd n) (Fin.natAdd n)).trace := by
  simp [trace, mul_apply, Fin.sum_univ_add, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr,
    -Fin.natAdd_eq_addNat]

/-- trace of a product of PSD matrices is nonnegative -/
lemma sddD_trace_psd {n : ℕ} {P X : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ (P * X).trace := by
  obtain ⟨k, v, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.1 hX
  rw [Matrix.mul_sum, trace_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [mul_vecMulVec, trace_vecMulVec]
  have := hP.dotProduct_mulVec_nonneg (v i)
  simp only [star_trivial] at this ⊢
  rw [dotProduct_comm]; exact this

lemma sddD_pd_lower {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) :
    ∃ c > 0, ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x) := by
  set K := Metric.sphere (0 : Fin n → ℝ) 1 with hK
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (P *ᵥ x) := by fun_prop
  have hdot_le : ∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ n * ‖x‖ ^ 2 := by
    intro x
    have : ∀ i, x i * x i ≤ ‖x‖ ^ 2 := fun i => by
      have h := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at h
      nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
    calc x ⬝ᵥ x = ∑ i, x i * x i := rfl
      _ ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = n * ‖x‖ ^ 2 := by simp
  have hscale : ∀ x : Fin n → ℝ, x ≠ 0 → ‖x‖⁻¹ • x ∈ K := by
    intro x hx
    rw [hK, mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0K, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne
      hcont.continuousOn
    have hx0 : x0 ≠ 0 := by
      rintro rfl; simp at hx0K
    have hc0 : 0 < x0 ⬝ᵥ (P *ᵥ x0) := by
      have := hP.dotProduct_mulVec_pos hx0
      simpa using this
    refine ⟨x0 ⬝ᵥ (P *ᵥ x0) / (n + 1), by positivity, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    have hu := hmin (hscale x hx)
    have hu' : x0 ⬝ᵥ (P *ᵥ x0) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (P *ᵥ (‖x‖⁻¹ • x)) := hu
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hu'
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hq : ‖x‖ ^ 2 * (x0 ⬝ᵥ (P *ᵥ x0)) ≤ x ⬝ᵥ (P *ᵥ x) := by
      have : ‖x‖ ^ 2 * (‖x‖⁻¹ * (‖x‖⁻¹ * (x ⬝ᵥ (P *ᵥ x)))) = x ⬝ᵥ (P *ᵥ x) := by
        field_simp
      calc _ ≤ ‖x‖ ^ 2 * (‖x‖⁻¹ * (‖x‖⁻¹ * (x ⬝ᵥ (P *ᵥ x)))) :=
            mul_le_mul_of_nonneg_left hu' (by positivity)
        _ = _ := this
    have h1 := hdot_le x
    have hd0 : 0 ≤ x ⬝ᵥ x := by
      simpa using (PosSemidef.one (n := Fin n) (R := ℝ)).dotProduct_mulVec_nonneg x
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖x‖]
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    exact absurd ⟨_, hscale x hx⟩ hne

lemma sddD_herm_lower {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    -((∑ i, ∑ j, |Q i j|) * (x ⬝ᵥ x)) ≤ x ⬝ᵥ (Q *ᵥ x) := by
  set u := x
  have hsq : ∀ i, u i ^ 2 ≤ u ⬝ᵥ u := fun i => by
    simpa [dotProduct, sq] using Finset.single_le_sum (f := fun k => u k * u k)
      (fun k _ => mul_self_nonneg (u k)) (Finset.mem_univ i)
  have hterm : ∀ i j, -(|Q i j| * (u ⬝ᵥ u)) ≤ u i * (Q i j * u j) := by
    intro i j
    have h1 : |u i * u j| ≤ u ⬝ᵥ u := by
      rw [abs_mul]
      nlinarith [abs_nonneg (u i), abs_nonneg (u j), sq_abs (u i), sq_abs (u j), hsq i, hsq j,
        sq_nonneg (|u i| - |u j|)]
    have h2 : |u i * (Q i j * u j)| = |Q i j| * |u i * u j| := by
      simp only [abs_mul]; ring
    have h3 := neg_abs_le (u i * (Q i j * u j))
    nlinarith [abs_nonneg (Q i j)]
  have : u ⬝ᵥ (Q *ᵥ u) = ∑ i, ∑ j, u i * (Q i j * u j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  rw [this, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun j _ => hterm i j

lemma sddD_shift {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) (hQ : Q.IsHermitian) :
    ∃ t : ℝ, 0 ≤ t ∧ (t • P + Q).PosDef := by
  obtain ⟨c, hc, hcP⟩ := sddD_pd_lower hP
  set s := ∑ i, ∑ j, |Q i j|
  have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(s + 1) / c, by positivity, ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · exact (hP.posSemidef.smul (a := (s + 1) / c) (by positivity)).isHermitian.add hQ
  simp only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h1 := hcP x
  have h2 := sddD_herm_lower Q x
  have hpos : 0 < x ⬝ᵥ x := by
    simpa using (PosDef.one (n := Fin n) (R := ℝ)).dotProduct_mulVec_pos hx
  have : (s + 1) / c * (x ⬝ᵥ (P *ᵥ x)) ≥ (s + 1) * (x ⬝ᵥ x) := by
    rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hc]
    nlinarith
  nlinarith

/-- constraint matrices of the VB encoding -/
noncomputable def sddD_Fs {n m : ℕ} (S : QuadraticSystem n m) :
    Fin m → Matrix (Fin (n+m)) (Fin (n+m)) ℝ :=
  fun i => sddD_bd (S.B i) (diagonal (Pi.single i 1))

lemma sddD_lmi_eq {n m : ℕ} (S : QuadraticSystem n m) (x : Fin m → ℝ) :
    VBSDP.Duality.lmi (sddD_bd (-S.A) 0) (sddD_Fs S) x =
      sddD_bd (∑ i, x i • S.B i - S.A) (diagonal x) := by
  ext a c
  induction a using Fin.addCases <;> induction c using Fin.addCases <;>
    simp [VBSDP.Duality.lmi, sddD_Fs, Matrix.sum_apply, diagonal_apply, Pi.single_apply,
      -Fin.natAdd_eq_addNat, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr]
  ring

lemma sddD_Fs_trace {n m : ℕ} (S : QuadraticSystem n m) (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ)
    (i : Fin m) :
    (sddD_Fs S i * Z).trace = (S.B i * Z.submatrix (Fin.castAdd m) (Fin.castAdd m)).trace
      + Z (Fin.natAdd n i) (Fin.natAdd n i) := by
  rw [sddD_Fs, sddD_bd_trace]
  congr 1
  simp [trace, diagonal_mul, Pi.single_apply]

lemma sddD_F0_trace {n m : ℕ} (S : QuadraticSystem n m) (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ) :
    -(sddD_bd (-S.A) 0 * Z).trace = (S.A * Z.submatrix (Fin.castAdd m) (Fin.castAdd m)).trace := by
  rw [sddD_bd_trace]
  simp [neg_mul, trace_neg]

lemma sddD_weak {n m : ℕ} (S : QuadraticSystem n m) {lam : Fin m → ℝ} (hlam : S.SDDFeasible lam)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : S.SDPFeasible X) :
    (S.A * X).trace ≤ ∑ i, lam i * S.d i := by
  have h0 := sddD_trace_psd hlam.1 hX.2
  have hexp : ((∑ i, lam i • S.B i - S.A) * X).trace = ∑ i, lam i * (S.B i * X).trace
      - (S.A * X).trace := by
    simp [sub_mul, Finset.sum_mul, trace_sub, trace_sum, trace_smul]
  have h1 : ∑ i, lam i * (S.B i * X).trace ≤ ∑ i, lam i * S.d i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hX.1 i) (hlam.2 i)
  linarith

theorem ny_sdd {n m : ℕ} (S : QuadraticSystem n m)
    (hB : ∀ i, (S.B i).IsHermitian) (hd : ∀ i, 0 ≤ S.d i)
    (hstrict : S.StrictlyFeasible)
    (hpd : ∃ μ : Fin m → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • S.B i).PosDef)
    (hAh : S.A.IsHermitian)
    (Fstar : ℝ) (hF : S.IsSDPValue Fstar) :
    S.SDDSolvableWithValue Fstar := by
  classical
  obtain ⟨μ, hμ0, hμpd⟩ := hpd
  have hF0 : (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)).IsHermitian := sddD_bd_herm hAh.neg isHermitian_zero
  have hFs : ∀ i, (sddD_Fs S i).IsHermitian := fun i =>
    sddD_bd_herm (hB i) (isHermitian_diagonal _)
  -- primal strict feasibility
  have hQ : (∑ i, S.B i - S.A).IsHermitian := by
    refine IsHermitian.sub ?_ hAh
    rw [IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => hB i
  obtain ⟨t, ht, htpd⟩ := sddD_shift hμpd hQ
  have hprim : ∃ x, (VBSDP.Duality.lmi (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)) (sddD_Fs S) x).PosDef := by
    refine ⟨fun i => t * μ i + 1, ?_⟩
    rw [sddD_lmi_eq]
    refine sddD_bd_posDef ?_ ?_
    · convert htpd using 1
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, one_smul, Finset.smul_sum]
      abel
    · rw [posDef_diagonal_iff]
      intro i
      have := hμ0 i
      positivity
  -- dual strict feasibility
  obtain ⟨x0, hx0⟩ := hstrict
  have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ∀ i, ε * (S.B i).trace < S.d i - x0 ⬝ᵥ (S.B i *ᵥ x0) := by
    rw [Filter.eventually_all]
    intro i
    have hlim : Filter.Tendsto (fun ε : ℝ => ε * (S.B i).trace) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (0 * (S.B i).trace)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds (Filter.tendsto_id.mul_const _))
    rw [zero_mul] at hlim
    exact hlim.eventually (gt_mem_nhds (by linarith [hx0 i]))
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hεpos' : 0 < ε := hεpos
  set Z11 : Matrix (Fin n) (Fin n) ℝ := vecMulVec x0 x0 + ε • 1 with hZ11
  have hZ11pd : Z11.PosDef := by
    have h1 := posSemidef_vecMulVec_self_star x0
    have h1' : (vecMulVec x0 x0).PosSemidef := by simpa using h1
    exact PosDef.posSemidef_add h1' (PosDef.one.smul hεpos')
  have hBZ : ∀ i, (S.B i * Z11).trace = x0 ⬝ᵥ (S.B i *ᵥ x0) + ε * (S.B i).trace := by
    intro i
    rw [hZ11, mul_add, trace_add, mul_vecMulVec, trace_vecMulVec, dotProduct_comm, mul_smul_comm,
      mul_one, trace_smul, smul_eq_mul]
  have hdual : ∃ Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ, Z.PosDef ∧
      ∀ i, (sddD_Fs S i * Z).trace = S.d i := by
    refine ⟨sddD_bd Z11 (diagonal fun i => S.d i - (S.B i * Z11).trace), sddD_bd_posDef hZ11pd ?_,
      fun i => ?_⟩
    · rw [posDef_diagonal_iff]
      intro i
      have := hε i
      rw [hBZ]
      linarith
    · rw [sddD_Fs_trace]
      have e1 : (sddD_bd Z11 (diagonal fun i => S.d i - (S.B i * Z11).trace)).submatrix
          (Fin.castAdd m) (Fin.castAdd m) = Z11 := by
        ext a b; simp [sddD_bd_ll]
      rw [e1, sddD_bd_rr]
      simp
  have key := VBSDP.Duality.theorem_3_1 S.d (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)) (sddD_Fs S) hF0 hFs
  have hpd_eq := key.1 (Or.inl hprim)
  obtain ⟨lam, hlamf, hlamv⟩ := (key.2 ⟨hprim, hdual⟩).1
  have hlamf' : (sddD_bd (∑ i, lam i • S.B i - S.A) (diagonal lam)).PosSemidef := by
    have := hlamf
    unfold VBSDP.Duality.IsPrimalFeasible at this
    rwa [sddD_lmi_eq] at this
  have hfeas : S.SDDFeasible lam := by
    refine ⟨sddD_bd_psd_left hlamf', fun i => ?_⟩
    have := (sddD_bd_psd_right hlamf').diag_nonneg (i := i)
    simpa using this
  have hval : S.d ⬝ᵥ lam = ∑ i, lam i * S.d i := by
    simp [dotProduct, mul_comm]
  have hlow : ∀ lam', S.SDDFeasible lam' → Fstar ≤ ∑ i, lam' i * S.d i := by
    intro lam' hl
    apply hF.2
    rintro _ ⟨X, hX, rfl⟩
    exact sddD_weak S hl hX
  have hup : VBSDP.Duality.dStar S.d (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)) (sddD_Fs S) ≤ (Fstar : EReal) := by
    apply sSup_le
    rintro _ ⟨Z, ⟨hZp, hZc⟩, rfl⟩
    rw [EReal.coe_le_coe_iff, sddD_F0_trace]
    apply hF.1
    refine ⟨_, ⟨fun i => ?_, hZp.submatrix _⟩, rfl⟩
    have h1 := hZc i
    rw [sddD_Fs_trace] at h1
    have h2 := hZp.diag_nonneg (i := Fin.natAdd n i)
    have h3 : 0 ≤ Z (Fin.natAdd n i) (Fin.natAdd n i) := h2
    linarith
  have hr : ∑ i, lam i * S.d i ≤ Fstar := by
    have h := hlamv.trans_le (hpd_eq.trans_le hup)
    rw [EReal.coe_le_coe_iff, hval] at h
    exact h
  refine ⟨⟨lam, hfeas, le_antisymm hr (hlow lam hfeas)⟩, ?_⟩
  rintro _ ⟨lam', hl, rfl⟩
  exact hlow lam' hl

end NY99

namespace NY99
open Matrix ModernConvex.Relaxations in
theorem ny_round {n m : ℕ} (S : QuadraticSystem n m)
    (hB : ∀ i, (S.B i).IsHermitian) (hcomm : ∀ i j, S.B i * S.B j = S.B j * S.B i)
    (hA : S.A.PosSemidef) (fstar : ℝ) (hf : S.IsPValue fstar)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : S.SDPFeasible X) :
    2 / Real.pi * (S.A * X).trace ≤ fstar :=
  ny_round_of_eig S (ny_eig S.B hB hcomm) hA fstar hf X hX
end NY99


open Matrix
open ModernConvex.Relaxations

namespace NY99

theorem main {n m : ℕ} (S : QuadraticSystem n m)
    (hB : ∀ i, (S.B i).IsHermitian) (hd : ∀ i, 0 ≤ S.d i)
    (hcomm : ∀ i j, S.B i * S.B j = S.B j * S.B i)
    (hstrict : S.StrictlyFeasible)
    (hpd : ∃ μ : Fin m → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • S.B i).PosDef)
    (hA : S.A.PosSemidef)
    (fstar Fstar : ℝ) (hf : S.IsPValue fstar) (hF : S.IsSDPValue Fstar) :
    0 ≤ fstar ∧ S.SDDSolvableWithValue Fstar ∧ Fstar ≤ Real.pi / 2 * fstar := by
  refine ⟨?_, ny_sdd S hB hd hstrict hpd hA.1 Fstar hF, ?_⟩
  · -- x = 0 solves the system
    have h0 : S.Solves 0 := fun i => by simpa using hd i
    have := hf.1 ⟨0, h0, rfl⟩
    simpa using this
  · refine hF.2 ?_
    rintro _ ⟨X, hX, rfl⟩
    have h := ny_round S hB hcomm hA fstar hf X hX
    have hpi := Real.pi_pos
    have : (S.A * X).trace = Real.pi / 2 * (2 / Real.pi * (S.A * X).trace) := by
      field_simp
    show (S.A * X).trace ≤ Real.pi / 2 * fstar
    rw [this]
    exact mul_le_mul_of_nonneg_left h (by positivity)

end NY99

open Matrix ModernConvex.Relaxations in
theorem solution {n m : ℕ} (S : QuadraticSystem n m)
    (hB : ∀ i, (S.B i).IsHermitian) (hd : ∀ i, 0 ≤ S.d i)
    (hcomm : ∀ i j, S.B i * S.B j = S.B j * S.B i)
    (hstrict : S.StrictlyFeasible)
    (hpd : ∃ μ : Fin m → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • S.B i).PosDef)
    (hA : S.A.PosSemidef)
    (fstar Fstar : ℝ) (hf : S.IsPValue fstar) (hF : S.IsSDPValue Fstar) :
    0 ≤ fstar ∧ S.SDDSolvableWithValue Fstar ∧ Fstar ≤ Real.pi / 2 * fstar :=
  NY99.main S hB hd hcomm hstrict hpd hA fstar Fstar hf hF
