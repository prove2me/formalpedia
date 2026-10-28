-- Prove2me | solution 1 for GeneralizedComplex.eq_bShift_symplecticGen_of_genType_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:31:34.41518+00:00
-- url     : https://prove2.me/submissions/b67e41e4-513e-4761-850d-b80e1efbdde9

import Definitions.Def_GeneralizedComplex_Basic

open Matrix GeneralizedComplex

namespace S215GCb

variable {N : ℕ}

noncomputable def eta (N : ℕ) : Matrix (GIdx N) (GIdx N) ℝ := fromBlocks 0 1 1 0

lemma elim_eq {α : Type*} (u : GIdx N → α) : u = Sum.elim (vecPart u) (formPart u) := by
  funext x; cases x <;> rfl

lemma pairing_eq (u v : GIdx N → ℝ) : pairing u v = (u ⬝ᵥ (eta N *ᵥ v)) / 2 := by
  conv_rhs => rw [elim_eq u, elim_eq v]
  simp only [eta, fromBlocks_mulVec, zero_mulVec, one_mulVec, zero_add, add_zero,
    Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim, pairing]
  rw [dotProduct_comm (vecPart u)]; ring

lemma mat_ext {ι : Type*} [Fintype ι] [DecidableEq ι] (M M' : Matrix ι ι ℝ)
    (h : ∀ u v, u ⬝ᵥ (M *ᵥ v) = u ⬝ᵥ (M' *ᵥ v)) : M = M' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single_one, single_dotProduct] using this

lemma cmul (M : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    M.map (fun r : ℝ => (r : ℂ)) *ᵥ (fun i => (x i : ℂ)) = fun i => ((M *ᵥ x) i : ℂ) := by
  funext i; simp [mulVec, dotProduct]

end S215GCb

open S215GCb in
theorem solution {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ)
    (hJ : IsGenAlmostComplex J) (h0 : genType (plusIEigenspace J) = 0) :
    ∃ B ω : Matrix (Fin N) (Fin N) ℝ, Bᵀ = -B ∧ ωᵀ = -ω ∧ ω.det ≠ 0 ∧
      J = bShift B * symplecticGen ω * bShift (-B) := by
  set a := J.toBlocks₁₁
  set b := J.toBlocks₁₂
  set c := J.toBlocks₂₁
  set d := J.toBlocks₂₂
  have hJb : J = fromBlocks a b c d := (fromBlocks_toBlocks J).symm
  have hsq := hJ.sq_eq_neg_one
  rw [hJb, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg, neg_zero] at hsq
  obtain ⟨e1, e2, e3, e4⟩ := fromBlocks_inj.mp hsq
  have hmat : Jᵀ * eta N * J = eta N := by
    apply mat_ext
    intro u v
    have := hJ.pairing_mulVec u v
    rw [pairing_eq, pairing_eq] at this
    have h' : (J *ᵥ u) ⬝ᵥ (eta N *ᵥ (J *ᵥ v)) = u ⬝ᵥ (eta N *ᵥ v) := by linarith
    rw [← h', Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u,
      vecMul_transpose]
  have hmat2 : Jᵀ * eta N * J * J = eta N * J := by rw [hmat]
  rw [Matrix.mul_assoc, hJ.sq_eq_neg_one, mul_neg, mul_one, hJb] at hmat2
  simp only [eta, fromBlocks_transpose, fromBlocks_multiply, mul_zero, mul_one, zero_mul,
    one_mul, zero_add, add_zero, fromBlocks_neg] at hmat2
  obtain ⟨-, hda, -, hbT⟩ := fromBlocks_inj.mp hmat2
  -- hda : -aᵀ = d, hbT : -bᵀ = b
  have hbdξ0 : b * d = -(a * b) := eq_neg_of_add_eq_zero_right e2
  have hdd : d * d = -1 - c * b := by rw [← e4]; abel
  set ac := a.map (fun r : ℝ => (r : ℂ))
  set bc := b.map (fun r : ℝ => (r : ℂ))
  set cc := c.map (fun r : ℝ => (r : ℂ))
  set dc := d.map (fun r : ℝ => (r : ℂ))
  have hJc : J.map (fun r : ℝ => (r : ℂ)) = fromBlocks ac bc cc dc := by
    rw [hJb, fromBlocks_map]
  have hacT : acᵀ = -dc := by
    ext i j; simp only [ac, dc, transpose_apply, map_apply]; rw [← hda]; simp
  have hbcT : bcᵀ = -bc := by
    ext i j; simp only [bc, transpose_apply, map_apply]
    conv_rhs => rw [← hbT]
    simp
  have hb : b.det ≠ 0 := by
    intro hdet
    obtain ⟨ξ, hξ0, hbξ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hbdξ : b *ᵥ (d *ᵥ ξ) = 0 := by
      rw [mulVec_mulVec, hbdξ0, neg_mulVec, ← mulVec_mulVec, hbξ, mulVec_zero, neg_zero]
    have hddξ : d *ᵥ (d *ᵥ ξ) = -ξ := by
      rw [mulVec_mulVec, hdd, sub_mulVec, neg_mulVec, one_mulVec, ← mulVec_mulVec, hbξ,
        mulVec_zero, sub_zero]
    set ζ : Fin N → ℂ := (fun i => (ξ i : ℂ)) - Complex.I • (fun i => ((d *ᵥ ξ) i : ℂ)) with hζ
    have hdζ : dc *ᵥ ζ = Complex.I • ζ := by
      rw [hζ, mulVec_sub, mulVec_smul, cmul, cmul, hddξ]
      funext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      push_cast; linear_combination (((d *ᵥ ξ) i : ℂ)) * Complex.I_sq
    have hbζ : bc *ᵥ ζ = 0 := by
      rw [hζ, mulVec_sub, mulVec_smul, cmul, cmul, hbdξ, hbξ]
      funext i; simp
    have hmemζ : (Sum.elim 0 ζ : GIdx N → ℂ) ∈ plusIEigenspace J := by
      simp only [plusIEigenspace, LinearMap.mem_ker, LinearMap.sub_apply, mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hJc]
      rw [fromBlocks_mulVec]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_add, hbζ, hdζ]
      funext x; cases x <;> simp
    have htop : tangentProjection (plusIEigenspace J) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_le (tangentProjection (plusIEigenspace J))
      simp only [Module.finrank_fin_fun] at h1 ⊢
      unfold genType at h0
      omega
    have hortho : ∀ v ∈ plusIEigenspace J, ζ ⬝ᵥ (v ∘ Sum.inl) = 0 := by
      intro v hv
      simp only [plusIEigenspace, LinearMap.mem_ker, LinearMap.sub_apply, mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hJc] at hv
      have hX : ac *ᵥ (v ∘ Sum.inl) + bc *ᵥ (v ∘ Sum.inr) = Complex.I • (v ∘ Sum.inl) := by
        funext i
        have := congrFun hv (Sum.inl i)
        rw [fromBlocks_mulVec] at this
        simpa using this
      have hA : ζ ⬝ᵥ (ac *ᵥ (v ∘ Sum.inl)) = -(Complex.I * (ζ ⬝ᵥ (v ∘ Sum.inl))) := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hacT, neg_mulVec, hdζ, neg_dotProduct,
          smul_dotProduct, smul_eq_mul]
      have hB : ζ ⬝ᵥ (bc *ᵥ (v ∘ Sum.inr)) = 0 := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hbcT, neg_mulVec, hbζ, neg_zero,
          zero_dotProduct]
      have hC := congrArg (ζ ⬝ᵥ ·) hX
      simp only [dotProduct_add, hA, hB, dotProduct_smul, smul_eq_mul] at hC
      have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp
      have : (2 * Complex.I) * (ζ ⬝ᵥ (v ∘ Sum.inl)) = 0 := by linear_combination -hC
      exact (mul_eq_zero.mp this).resolve_left hI
    apply hξ0
    funext j
    have hj : (Pi.single j 1 : Fin N → ℂ) ∈ tangentProjection (plusIEigenspace J) := by
      rw [htop]; trivial
    obtain ⟨v, hv, hvj⟩ := Submodule.mem_map.mp hj
    have := hortho v hv
    have hvj' : v ∘ Sum.inl = Pi.single j 1 := hvj
    rw [hvj', dotProduct_single, mul_one, hζ] at this
    have := congrArg Complex.re this
    simpa using this
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr hb
  have hbT' : bᵀ = -b := neg_eq_iff_eq_neg.mp hbT
  have hbinvT : (b⁻¹)ᵀ = -b⁻¹ := by
    rw [transpose_nonsing_inv, hbT']
    exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, nonsing_inv_mul _ hbu])
  have hs : -((b⁻¹)ᵀ)⁻¹ = b := by
    rw [transpose_nonsing_inv, nonsing_inv_nonsing_inv _ (by rwa [det_transpose]), hbT', neg_neg]
  have hd : d = -(b⁻¹ * a * b) := by
    rw [← nonsing_inv_mul_cancel_left b d hbu, hbdξ0, Matrix.mul_neg, Matrix.mul_assoc]
  have hc : c = -b⁻¹ - b⁻¹ * a * a := by
    have : b * c = -1 - a * a := by rw [← e1]; abel
    rw [← nonsing_inv_mul_cancel_left b c hbu, this, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_one, Matrix.mul_assoc]
  have haT : aᵀ = -d := neg_eq_iff_eq_neg.mp hda
  have hsym : symplecticGen b⁻¹ = fromBlocks 0 b (-b⁻¹) 0 := by
    unfold symplecticGen; rw [hs, hbinvT]
  refine ⟨-(b⁻¹ * a)ᵀ, b⁻¹, ?_, hbinvT, (isUnit_nonsing_inv_det b hbu).ne_zero, ?_⟩
  · rw [transpose_neg, transpose_transpose, neg_neg, transpose_mul, haT, hbinvT, neg_mul_neg, hd,
      Matrix.neg_mul, mul_nonsing_inv_cancel_right b _ hbu]
  · rw [hJb]
    rw [hsym]
    simp only [bShift, transpose_neg, transpose_transpose, neg_neg,
      fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    rw [hd, hc]
    congr 1
    · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hbu, Matrix.one_mul]
    · rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc (b⁻¹ * a) b, ← Matrix.mul_assoc b,
        mul_nonsing_inv _ hbu, Matrix.one_mul, sub_eq_add_neg]
    · rw [Matrix.neg_mul]

