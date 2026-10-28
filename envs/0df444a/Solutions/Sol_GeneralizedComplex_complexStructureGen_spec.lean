-- Prove2me | solution 1 for GeneralizedComplex.complexStructureGen_spec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:03:58.725425+00:00
-- url     : https://prove2.me/submissions/f0f1ddd4-eb77-4e06-9d3a-8949662e3f22

import Definitions.Def_GeneralizedComplex_Basic

open Matrix GeneralizedComplex
open scoped ComplexOrder

namespace S215GC

variable {N : ℕ}

/-- Kernel dimension of a complex square matrix. -/
lemma finrank_ker_add_rank (M : Matrix (Fin N) (Fin N) ℂ) :
    M.rank + Module.finrank ℂ (LinearMap.ker M.mulVecLin) = N := by
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  simpa [Matrix.rank] using this

lemma rank_map_star (M : Matrix (Fin N) (Fin N) ℂ) : (M.map star).rank = M.rank := by
  have : M.map star = Mᴴᵀ := by ext i j; simp [conjTranspose_apply]
  rw [this, rank_transpose, rank_conjTranspose]

end S215GC

open S215GC in
theorem solution {N : ℕ} (J₀ : Matrix (Fin N) (Fin N) ℝ) (hJ₀ : J₀ * J₀ = -1) :
    IsGenAlmostComplex (complexStructureGen J₀) ∧
      genType (plusIEigenspace (complexStructureGen J₀)) = N := by
  have hT : J₀ᵀ * J₀ᵀ = -1 := by rw [← transpose_mul, hJ₀, transpose_neg, transpose_one]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [complexStructureGen, fromBlocks_multiply, neg_mul, mul_neg, neg_neg, hJ₀, hT,
      mul_zero, zero_mul, add_zero, zero_add]
    rw [← fromBlocks_one, fromBlocks_neg, neg_zero]
  · intro u v
    have hf : ∀ a b : Fin N → ℝ, formPart (Sum.elim a b) = b := fun _ _ => rfl
    have hv : ∀ a b : Fin N → ℝ, vecPart (Sum.elim a b) = a := fun _ _ => rfl
    simp only [pairing, complexStructureGen, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, hf, hv]
    have key : ∀ x y : Fin N → ℝ, (J₀ᵀ *ᵥ x) ⬝ᵥ (-J₀ *ᵥ y) = x ⬝ᵥ y := by
      intro x y
      rw [mulVec_transpose, ← dotProduct_mulVec, neg_mulVec, mulVec_neg, mulVec_mulVec, hJ₀,
        neg_mulVec, one_mulVec, neg_neg]
    rw [key, key]
    rfl
  · -- the complexified matrices
    set Jc : Matrix (Fin N) (Fin N) ℂ := J₀.map (fun x : ℝ => (x : ℂ)) with hJc
    have hJc2 : Jc * Jc = -1 := by
      have : Jc * Jc = (J₀ * J₀).map Complex.ofRealHom := (Matrix.map_mul (f := Complex.ofRealHom)).symm
      ext i j; rw [this, hJ₀]; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    set Mp : Matrix (Fin N) (Fin N) ℂ := Jc + Complex.I • 1
    set Mm : Matrix (Fin N) (Fin N) ℂ := Jc - Complex.I • 1
    have hstar : Mm.map star = Mp := by
      ext i j
      simp only [Mm, Mp, map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, one_apply, hJc, smul_eq_mul,
        star_sub, Complex.star_def, Complex.conj_ofReal, map_mul, Complex.conj_I]
      split_ifs <;> simp
    have hprod : Mm * Mp = 0 := by
      simp only [Mm, Mp, sub_mul, mul_add, hJc2, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
        smul_smul, Complex.I_mul_I]
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
    -- the tangent projection is ker Mp
    have hproj : tangentProjection (plusIEigenspace (complexStructureGen J₀)) =
        LinearMap.ker Mp.mulVecLin := by
      have hmap : (complexStructureGen J₀).map (fun x : ℝ => (x : ℂ)) = fromBlocks (-Jc) 0 0 Jcᵀ := by
        simp only [complexStructureGen, fromBlocks_map, hJc]
        congr 1 <;> ext i j <;> simp
      ext X
      simp only [tangentProjection, plusIEigenspace, Submodule.mem_map, LinearMap.mem_ker,
        LinearMap.sub_apply, mulVecLin_apply, LinearMap.smul_apply, LinearMap.id_apply, hmap,
        sub_eq_zero, LinearMap.funLeft_apply]
      constructor
      · rintro ⟨v, hv, rfl⟩
        have h1 := congrFun hv
        have hX : ∀ i, (-Jc *ᵥ (v ∘ Sum.inl)) i = Complex.I * v (Sum.inl i) := by
          intro i
          have := h1 (Sum.inl i)
          simpa [fromBlocks_mulVec] using this
        change Mp *ᵥ (v ∘ Sum.inl) = 0
        ext i
        have := hX i
        simp only [Mp, add_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Pi.zero_apply, neg_mulVec, Pi.neg_apply] at this ⊢
        rw [neg_eq_iff_eq_neg] at this
        rw [this]; simp only [Function.comp_apply]; ring
      · intro hX
        refine ⟨Sum.elim X 0, ?_, rfl⟩
        ext p
        rcases p with i | i
        · have := congrFun hX i
          simp only [Mp, add_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, Pi.zero_apply] at this
          simp [fromBlocks_mulVec, Function.comp_def, neg_mulVec, smul_mulVec]
          linear_combination -this
        · simp [fromBlocks_mulVec, Function.comp_def]
          exact congrFun (Matrix.mulVec_zero Jcᵀ) i
    -- dimension count
    set k := Module.finrank ℂ (LinearMap.ker Mp.mulVecLin)
    have hrk : Mp.rank = Mm.rank := by rw [← hstar, rank_map_star]
    have h1 := finrank_ker_add_rank Mp
    have h2 := finrank_ker_add_rank Mm
    -- range Mp ⊆ ker Mm
    have hle : Mp.rank ≤ Module.finrank ℂ (LinearMap.ker Mm.mulVecLin) := by
      apply Submodule.finrank_mono
      rintro _ ⟨x, rfl⟩
      simp only [LinearMap.mem_ker, mulVecLin_apply, mulVec_mulVec, hprod, zero_mulVec]
    -- ker Mp ⊓ ker Mm = ⊥
    have hinf : LinearMap.ker Mp.mulVecLin ⊓ LinearMap.ker Mm.mulVecLin = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hp, hm⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, mulVecLin_apply] at hp hm
      have : Mp *ᵥ x - Mm *ᵥ x = (2 * Complex.I) • x := by
        simp only [Mp, Mm, add_mulVec, sub_mulVec, smul_mulVec, one_mulVec]
        ext j; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hp, hm, sub_zero] at this
      have h2I : (2 * Complex.I) ≠ 0 := by simp
      exact (Submodule.mem_bot ℂ).mpr ((smul_eq_zero.mp this.symm).resolve_left h2I)
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker Mp.mulVecLin)
      (LinearMap.ker Mm.mulVecLin)
    rw [hinf, finrank_bot] at hsum
    have hsupN : Module.finrank ℂ ↥(LinearMap.ker Mp.mulVecLin ⊔ LinearMap.ker Mm.mulVecLin) ≤ N := by
      have := Submodule.finrank_le (LinearMap.ker Mp.mulVecLin ⊔ LinearMap.ker Mm.mulVecLin)
      simpa using this
    unfold genType
    rw [hproj]
    omega
