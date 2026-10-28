-- Prove2me | solution 1 for OAI.DimensionTen.linear_composite_not_separable_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:01:37.297006+00:00
-- url     : https://prove2.me/submissions/8d9a7a4b-25e8-44d9-a526-53c9255d365b

import Mathlib
import Definitions.Def_DimensionTenChannel
import Definitions.Def_OAIQ057D013
import Theorems.Thm_OAI_DimensionTen_Border_rank_points_s2
import Theorems.Thm_OAI_DimensionTen_compositeChoi_veronese_s2
import Theorems.Thm_OAI_DimensionTen_veronese_family_general_position_s2

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen

theorem blocks_conjTranspose (i : Fin 4) : (blocks i)ᴴ = (blocks i)ᵀ := by
  ext a b
  simp [blocks, Matrix.conjTranspose_apply]

theorem pencilMap_projector_gram (x : Fin 4 → ℂ) :
    pencilMap (projector x) = (pencil x)ᴴ * pencil x := by
  simp only [pencilMap, projector, Matrix.vecMulVec_apply, Pi.star_apply, pencil,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, blocks_conjTranspose,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

theorem pencilMap_projector_rank (x : Fin 4 → ℂ) :
    (pencilMap (projector x)).rank = (pencil x).rank := by
  rw [pencilMap_projector_gram, Matrix.rank_conjTranspose_mul_self]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PureMatrices
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma pure_posSemidef {n : Type*} [Fintype n] (x : n → ℂ) : (pure x).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star x

lemma product_dot {a b : ℕ} (x y : Fin a → ℂ) (u v : Fin b → ℂ) :
    star (productVector x u) ⬝ᵥ productVector y v =
      (star x ⬝ᵥ y) * (star u ⬝ᵥ v) := by
  simp only [dotProduct, Fintype.sum_prod_type, productVector, Pi.star_apply,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma choi_eq_amplify {a b : ℕ} (F : Mat a → Mat b) :
    choi F = amplify F a (pure (omega a)) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  change F (Matrix.single i j 1) u v = F (fun p q => pure (omega a) (i,p) (j,q)) u v
  congr 2
  ext p q
  simp [pure, omega, Matrix.single_apply, Matrix.vecMulVec_apply, ite_and]
  split_ifs <;> simp_all

lemma cp_choi_posSemidef {a b : ℕ} (F : Mat a → Mat b) (hF : CompletelyPositive F)
    (ha : 0 < a) : (choi F).PosSemidef := by
  rw [choi_eq_amplify]
  exact hF a ha _ (pure_posSemidef _)

lemma cp_comp {a b c : ℕ} (F : Mat a → Mat b) (G : Mat b → Mat c)
    (hF : CompletelyPositive F) (hG : CompletelyPositive G) :
    CompletelyPositive (G ∘ F) := by
  intro k hk X hX
  exact hG k hk _ (hF k hk X hX)

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorSymmetry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma firstSix_real : firstSixᴴ = firstSixᵀ := by
  ext i j
  simp [firstSix, Matrix.conjTranspose_apply, apply_ite star]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorMaps
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma phiOne_kraus : phiOne = krausMap phiOneKraus := by
  funext A
  unfold phiOne
  rw [exteriorMap_input_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma phiOne_output_transpose (A : Mat 10) : (phiOne A)ᵀ = phiOne A := by
  unfold phiOne
  rw [real_embedding_transpose _ firstSix_real, exteriorMap_output_transpose]

lemma phiOne_ppt : PPT phiOne := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiOne_kraus]; exact krausMap_linear _
  · rw [phiOne_kraus]; exact krausMap_cp _
  · simp only [phiOne_output_transpose]
    rw [phiOne_kraus]; exact krausMap_cp _

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorEvaluation
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma compositeChoi_posSemidef : compositeChoi.PosSemidef := by
  exact cp_choi_posSemidef _ (cp_comp _ _ phiOne_ppt.2.1 phiTwo_ppt.2.1) (by decide)

end DimensionTen

end
end

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix
namespace DimensionTen
lemma blocksZ_zero_gram : (blocksZ 0)ᵀ * blocksZ 0 = (36:ℤ) • (1:Matrix (Fin 4) (Fin 4) ℤ) := by
  decide
lemma blocks_zero_gram : (blocks 0)ᴴ * blocks 0 = (36:ℂ) • (1:Mat 4) := by
  rw [blocks_conjTranspose]
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ => A.map (Int.castRingHom ℂ)) blocksZ_zero_gram
  have hm : ((36:ℤ) • (1:Matrix (Fin 4) (Fin 4) ℤ)).map (Int.castRingHom ℂ) =
      (36:ℂ) • (1:Mat 4) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.map_apply, Matrix.ofNat_apply]
  rw [hm] at h
  simpa only [Matrix.map_mul, Matrix.transpose_map, blocks] using h

lemma pencil_ezero : pencil (![1,0,0,0] : Fin 4 → ℂ) = blocks 0 := by
  simp [pencil, Fin.sum_univ_succ]
lemma pencilMap_ezero_fast : pencilMap (pure (![1,0,0,0] : Fin 4 → ℂ)) =
    (36 : ℂ) • (1 : Mat 4) := by
  change pencilMap (projector (![1,0,0,0] : Fin 4 → ℂ)) = _
  rw [pencilMap_projector_gram, pencil_ezero, blocks_zero_gram]
end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_FamilyGeometry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma no_two_zero_cover (p q : Fin 20 → ℂ)
    (hp : (Finset.univ.filter (fun k => p k = 0)).card ≤ 9)
    (hq : (Finset.univ.filter (fun k => q k = 0)).card ≤ 9)
    (h : ∀ k, p k = 0 ∨ q k = 0) : False := by
  classical
  have hs : Finset.univ ⊆ (Finset.univ.filter (fun k => p k = 0)) ∪
      (Finset.univ.filter (fun k => q k = 0)) := by
    intro k hk
    simpa using h k
  have hh := Finset.card_le_card hs
  have hu := Finset.card_union_le (Finset.univ.filter (fun k => p k = 0))
    (Finset.univ.filter (fun k => q k = 0))
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  omega

lemma kronecker_mul_product {a b : ℕ} (A : Mat a) (B : Mat b)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    (A ⊗ₖ B) *ᵥ productVector u v = productVector (A *ᵥ u) (B *ᵥ v) := by
  ext ⟨i,j⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, productVector,
    Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma kronecker_product_dot {a b : ℕ} (A : Mat a) (B : Mat b)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    star (productVector u v) ⬝ᵥ ((A ⊗ₖ B) *ᵥ productVector u v) =
      (star u ⬝ᵥ (A *ᵥ u)) * (star v ⬝ᵥ (B *ᵥ v)) := by
  rw [kronecker_mul_product, product_dot]

lemma psd_summand_kernel {r n : Type*} [Fintype r] [Fintype n]
    (A : r → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (v : n → ℂ)
    (hv : (∑ i, A i) *ᵥ v = 0) (i : r) : A i *ᵥ v = 0 := by
  have hs : ∑ j, star v ⬝ᵥ (A j *ᵥ v) = 0 := by
    rw [← dotProduct_sum, ← Matrix.sum_mulVec, hv, dotProduct_zero]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset r)) => (hA j).dotProduct_mulVec_nonneg v)).mp hs i
      (Finset.mem_univ i)
  exact ((hA i).dotProduct_mulVec_zero_iff _).mp hi

lemma matrix_nonzero_row {n : ℕ} {A : Mat n} (hA : A ≠ 0) :
    ∃ i : Fin n, star (A i) ≠ 0 := by
  by_contra hh
  push Not at hh
  apply hA
  ext i j
  have hi := congrFun (hh i) j
  simpa only [Pi.star_apply, Pi.zero_apply, star_eq_zero, Matrix.zero_apply] using hi

lemma nonseparable_of_kernel_family (X : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ)
    (hne : X ≠ 0) (f : Fin 20 → (Fin 10 → ℂ))
    (hpos : ∀ u : Fin 10 → ℂ, u ≠ 0 →
      (Finset.univ.filter (fun k => star u ⬝ᵥ f k = 0)).card ≤ 9)
    (hker : ∀ k, X *ᵥ productVector (f k) (f k) = 0) : ¬ separable X := by
  intro hsep
  obtain ⟨r, A, B, hAB, hsum⟩ := hsep
  have hi (i : Fin r) : A i = 0 ∨ B i = 0 := by
    by_cases hA : A i = 0
    · exact Or.inl hA
    by_cases hB : B i = 0
    · exact Or.inr hB
    exfalso
    obtain ⟨a, ha⟩ := matrix_nonzero_row hA
    obtain ⟨b, hb⟩ := matrix_nonzero_row hB
    apply no_two_zero_cover
      (fun k => star (star (A i a)) ⬝ᵥ f k) (fun k => star (star (B i b)) ⬝ᵥ f k)
      (hpos _ ha) (hpos _ hb)
    intro k
    have hk : (A i ⊗ₖ B i) *ᵥ productVector (f k) (f k) = 0 := by
      apply psd_summand_kernel (fun j => A j ⊗ₖ B j)
        (fun j => (hAB j).1.kronecker (hAB j).2) _ _ i
      simpa only [Matrix.kronecker] using hsum ▸ hker k
    have hd : (star (f k) ⬝ᵥ (A i *ᵥ f k)) * (star (f k) ⬝ᵥ (B i *ᵥ f k)) = 0 := by
      rw [← kronecker_product_dot, hk, dotProduct_zero]
    rcases mul_eq_zero.mp hd with h | h
    · left
      have hz := ((hAB i).1.dotProduct_mulVec_zero_iff _).mp h
      simpa only [star_star, Matrix.mulVec, Pi.zero_apply] using congrFun hz a
    · right
      have hz := ((hAB i).2.dotProduct_mulVec_zero_iff _).mp h
      simpa only [star_star, Matrix.mulVec, Pi.zero_apply] using congrFun hz b
  apply hne
  rw [hsum]
  apply Finset.sum_eq_zero
  intro i hi'
  rcases hi i with h | h <;> simp [h, Matrix.kronecker]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Main
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma pencilMap_det_zero_of_rank {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
    (pencilMap (pure x)).det = 0 := by
  by_contra h
  have hr := Matrix.rank_of_det_ne_zero h
  have he : (pencilMap (pure x)).rank = (pencil x).rank := pencilMap_projector_rank x
  rw [he] at hr
  norm_num at hr
  omega

lemma compositeChoi_kernel_rank {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
    compositeChoi *ᵥ productVector (veronese x) (veronese x) = 0 := by
  apply (compositeChoi_posSemidef.dotProduct_mulVec_zero_iff _).mp
  rw [compositeChoi_veronese_s2, pencilMap_det_zero_of_rank hx, mul_zero]

lemma pencilMap_ezero : pencilMap (pure (![1,0,0,0] : Fin 4 → ℂ)) =
    (36 : ℂ) • (1 : Mat 4) := by
  exact pencilMap_ezero_fast

lemma compositeChoi_ne : compositeChoi ≠ 0 := by
  intro hh
  have h := compositeChoi_veronese_s2 (![1,0,0,0] : Fin 4 → ℂ)
  rw [hh, Matrix.zero_mulVec, dotProduct_zero, pencilMap_ezero] at h
  norm_num [Matrix.det_smul] at h

lemma compositeChoi_not_separable : ¬ separable compositeChoi := by
  exact nonseparable_of_kernel_family _ compositeChoi_ne
    (fun k => veronese (chart (Border.points k))) veronese_family_general_position_s2
    (fun k => compositeChoi_kernel_rank (Border.rank_points_s2 k))


end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Channel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving PPT channel with an entangled square, from the dimension-ten pair. -/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace DimensionTen

@[simp] lemma phiOneLinear_apply (A : Mat 10) : phiOneLinear A = phiOne A := by
  rw [phiOne_kraus]
  simp only [phiOneLinear, LinearMap.sum_apply, ChannelCompletion.ad_apply, krausMap]

lemma linear_composite_choi :
    ChannelCompletion.choi (phiTwoLinear.comp phiOneLinear) = compositeChoi := by
  ext i j
  simp only [ChannelCompletion.choi, LinearMap.comp_apply,
    phiOneLinear_apply, phiTwoLinear_apply, compositeChoi, choi, Function.comp_apply]

lemma linear_composite_not_separable_s2_oai :
    ¬ ChannelCompletion.Separable
      (ChannelCompletion.choi (phiTwoLinear.comp phiOneLinear)) := by
  rw [linear_composite_choi]
  intro h
  obtain ⟨r, A, B, hA, hB, hsum⟩ := h
  exact compositeChoi_not_separable ⟨r, A, B, fun i => ⟨hA i, hB i⟩, hsum⟩

end DimensionTen

end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.linear_composite_not_separable_s2_oai := @OAI.DimensionTen.linear_composite_not_separable_s2_oai
