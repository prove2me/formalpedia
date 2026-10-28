-- Prove2me | solution 1 for OAI.DimensionTen.compositeChoi_kernel_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:05:47.26405+00:00
-- url     : https://prove2.me/submissions/4d1d3b2d-6043-412c-9f9d-10235f5183b5

import Mathlib
import Definitions.Def_DimensionTenPair
import Definitions.Def_OAIQ033D009

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilModel
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


theorem blocksZ_transpose_mul_comm (i j : Fin 4) :
    (blocksZ i)ᵀ * blocksZ j = (blocksZ j)ᵀ * blocksZ i := by
  decide +revert


theorem blocks_transpose_mul_comm (i j : Fin 4) :
    (blocks i)ᵀ * blocks j = (blocks j)ᵀ * blocks i := by
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ =>
    A.map (Int.castRingHom ℂ)) (blocksZ_transpose_mul_comm i j)
  simpa only [Matrix.map_mul, Matrix.transpose_map, blocks] using h

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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PureMatrices
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

lemma pure_conjugate {a b : Type*} [Fintype a] (V : Matrix b a ℂ) (x : a → ℂ) :
    V * pure x * Vᴴ = pure (V *ᵥ x) := by
  simp only [pure, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma pure_kronecker {a b : ℕ} (x : Fin a → ℂ) (y : Fin b → ℂ) :
    pure (productVector x y) = pure x ⊗ₖ pure y := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [pure, productVector, Matrix.vecMulVec_apply]
  ring

lemma trace_pure_mul {n : Type*} [Fintype n] (x : n → ℂ) (A : Matrix n n ℂ) :
    Matrix.trace (pure x * A) = star x ⬝ᵥ (A *ᵥ x) := by
  rw [pure, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

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

lemma linear_comp {a b c : ℕ} (F : Mat a → Mat b) (G : Mat b → Mat c)
    (hF : IsComplexLinear F) (hG : IsComplexLinear G) :
    IsComplexLinear (G ∘ F) := by
  constructor
  · intro A B; simp only [Function.comp_apply, hF.1, hG.1]
  · intro c A; simp only [Function.comp_apply, hF.2, hG.2]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Kraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

lemma krausMap_add {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A B : Matrix a a ℂ) :
    krausMap Q (A + B) = krausMap Q A + krausMap Q B := by
  simp [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma krausMap_smul {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (c : ℂ) (A : Matrix a a ℂ) :
    krausMap Q (c • A) = c • krausMap Q A := by
  simp [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma krausMap_linear {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : IsComplexLinear (krausMap Q) :=
  ⟨krausMap_add Q, krausMap_smul Q⟩

lemma posSemidef_sum {r n : Type*} [Fintype r] (A : r → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i, A i).PosSemidef := by
  classical
  have hh : ∀ s : Finset r, (∑ i ∈ s, A i).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
    | @insert i s hi ih => simpa [Finset.sum_insert hi] using (h i).add ih
  exact hh Finset.univ

lemma krausMap_positive {r a b : Type*} [Fintype r] [Fintype a] [Finite b]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    (krausMap Q A).PosSemidef := by
  exact posSemidef_sum _ (fun k => hA.mul_mul_conjTranspose_same (Q k))

lemma krausMap_entry {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (u v : b) :
    krausMap Q A u v = ∑ k, ∑ i, ∑ j, Q k u i * A i j * star (Q k v j) := by
  simp only [krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

lemma amplify_kraus {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (k : ℕ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    amplify (krausMap Q) k X = krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X := by
  ext u v
  change krausMap Q (fun i j => X (u.1, i) (v.1, j)) u.2 v.2 =
    krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X u v
  erw [krausMap_entry, krausMap_entry]
  have hentry (r : r) (u : Fin k × Fin b) (v : Fin k × Fin a) :
      ((1 : Mat k) ⊗ₖ Q r) u v = if u.1 = v.1 then Q r u.2 v.2 else 0 := by
    change (if u.1 = v.1 then (1 : ℂ) else 0) * Q r u.2 v.2 = _
    split <;> simp_all
  simp only [hentry]
  simp [Fintype.sum_prod_type, apply_ite star, ite_mul, mul_ite]

lemma krausMap_cp {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : CompletelyPositive (krausMap Q) := by
  intro k hk X hX
  rw [amplify_kraus]
  exact krausMap_positive _ X hX

lemma krausMap_single {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (i j : Fin a) (u v : Fin b) :
    krausMap Q (Matrix.single i j 1) u v = ∑ k, Q k u i * star (Q k v j) := by
  simp [krausMap_entry, Matrix.single_apply, ite_and]

lemma krausMap_adjoint {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) :
    hsAdjoint (krausMap Q) = krausMap (fun k => (Q k)ᴴ) := by
  funext A
  ext i j
  change (∑ u, ∑ v, star (krausMap Q (Matrix.single i j 1) u v) * A u v) = _
  simp only [krausMap_single]
  simp only [krausMap_entry,
    star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext v; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_TensorKraus
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

lemma sum_kronecker {r a b c d : Type*} [Fintype r]
    (A : r → Matrix a b ℂ) (B : Matrix c d ℂ) :
    (∑ r, A r) ⊗ₖ B = ∑ r, A r ⊗ₖ B := by
  ext i j
  simp [Matrix.sum_apply, Finset.sum_mul]

lemma kronecker_sum {r a b c d : Type*} [Fintype r]
    (A : Matrix a b ℂ) (B : r → Matrix c d ℂ) :
    A ⊗ₖ (∑ r, B r) = ∑ r, A ⊗ₖ B r := by
  ext i j
  simp [Matrix.sum_apply, Finset.mul_sum]

lemma block_expansion {a c : ℕ} (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    X = ∑ i : Fin c, ∑ j : Fin c,
      (Matrix.of (fun a b => X (a, i) (b, j))) ⊗ₖ (Matrix.single i j 1) := by
  ext ⟨u, i⟩ ⟨v, j⟩
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

lemma sum_four_comm {a b c d M : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [AddCommMonoid M] (f : a → b → c → d → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

lemma tensorMap_kraus {r s : Type*} [Fintype r] [Fintype s] {a b c d : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (R : s → Matrix (Fin d) (Fin c) ℂ)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap (krausMap Q) (krausMap R) X =
      krausMap (fun p : r × s => Q p.1 ⊗ₖ R p.2) X := by
  conv_rhs => arg 2; rw [block_expansion X]
  simp only [tensorMap, Matrix.kronecker, krausMap, Fintype.sum_prod_type, Matrix.conjTranspose_kronecker,
    Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
    sum_kronecker, kronecker_sum]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  exact sum_four_comm (fun (i j : Fin c) (k : r) (l : s) =>
    (Q k * Matrix.of (fun a b => X (a, i) (b, j)) * (Q k)ᴴ) ⊗ₖ
      (R l * Matrix.single i j 1 * (R l)ᴴ))

lemma krausMap_conjugate {r a b c d : Type*} [Fintype r] [Fintype a] [Fintype b]
    [Fintype c] (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (V : Matrix d b ℂ)
    (A : Matrix c c ℂ) :
    V * krausMap Q (U * A * Uᴴ) * Vᴴ =
      krausMap (fun k => V * Q k * U) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_postconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype b]
    (Q : r → Matrix b a ℂ) (V : Matrix c b ℂ) (A : Matrix a a ℂ) :
    V * krausMap Q A * Vᴴ = krausMap (fun k => V * Q k) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_preconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype c]
    (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (A : Matrix c c ℂ) :
    krausMap Q (U * A * Uᴴ) = krausMap (fun k => Q k * U) A := by
  simp only [krausMap, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ChoiPairing
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

lemma matrix_expansion {a : ℕ} (A : Mat a) :
    A = ∑ i : Fin a, ∑ j : Fin a, A i j • Matrix.single i j 1 := by
  ext i j
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

lemma linear_expansion {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F) (A : Mat a) :
    F A = ∑ i : Fin a, ∑ j : Fin a, A i j • F (Matrix.single i j 1) := by
  calc
    F A = F (∑ i, ∑ j, A i j • Matrix.single i j 1) := congrArg F (matrix_expansion A)
    _ = _ := by
      change asLinearMap F hF _ = _
      simp only [map_sum, map_smul, asLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

lemma choi_trace_pairing {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F)
    (A : Mat a) (B : Mat b) :
    Matrix.trace ((A ⊗ₖ B) * choi F) = Matrix.trace (B * F Aᵀ) := by
  rw [linear_expansion F hF Aᵀ]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, choi, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.transpose_apply, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma choi_product_dot {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    star (productVector u v) ⬝ᵥ (choi F *ᵥ productVector u v) =
      Matrix.trace (pure v * F (pure u)ᵀ) := by
  rw [← trace_pure_mul, pure_kronecker, choi_trace_pairing F hF]

lemma kraus_trace_adjoint {r a b : Type*} [Fintype r] [Fintype a] [Fintype b]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    Matrix.trace (A * krausMap (fun k => (Q k)ᴴ) B) =
      Matrix.trace (krausMap Q A * B) := by
  simp only [krausMap, Matrix.conjTranspose_conjTranspose, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    Matrix.trace (A * ((Q k)ᴴ * B * Q k)) =
      Matrix.trace ((A * (Q k)ᴴ * B) * Q k) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Q k * (A * (Q k)ᴴ * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_MinorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

 lemma det_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
     M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2 - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1 + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1 - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2 + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0 - M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0 + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1 - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0 + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0 - M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1 + M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0 - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_TensorSymmetry
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

lemma kronecker_transpose {a b c d : Type*} (A : Matrix a b ℂ) (B : Matrix c d ℂ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := rfl

lemma tensorMap_output_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, (F A)ᵀ = F A) (hG : ∀ A, (G A)ᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    (tensorMap F G X)ᵀ = tensorMap F G X := by
  simp only [tensorMap, Matrix.kronecker, Matrix.transpose_sum, kronecker_transpose, hG]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  erw [hF]

lemma tensorMap_input_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, F Aᵀ = F A) (hG : ∀ A, G Aᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap F G Xᵀ = tensorMap F G X := by
  unfold tensorMap
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hb : (fun a b => Xᵀ (a, j) (b, i)) =
      (Matrix.of (fun a b => X (a, i) (b, j)))ᵀ := rfl
  rw [hb, hF]
  have hg : G (Matrix.single j i 1) = G (Matrix.single i j 1) := by
    have ht : (Matrix.single i j (1 : ℂ))ᵀ = Matrix.single j i 1 := by
      simp only [Matrix.transpose_single]
    rw [← ht, hG]
  rw [hg]
  rfl

lemma hsAdjoint_output_transpose {a b : ℕ} (F : Mat a → Mat b)
    (h : ∀ A, F Aᵀ = F A) (Y : Mat b) :
    (hsAdjoint F Y)ᵀ = hsAdjoint F Y := by
  ext i j
  change (∑ u, ∑ v, star (F (Matrix.single j i 1) u v) * Y u v) = _
  have he : F (Matrix.single j i 1) = F (Matrix.single i j 1) := by
    rw [← Matrix.transpose_single, h]
  rw [he]
  rfl

lemma symmetricIsometry_real : symmetricIsometryᴴ = symmetricIsometryᵀ := by
  ext i j
  simp [symmetricIsometry, Matrix.conjTranspose_apply, apply_ite star]

lemma exteriorIsometry_real : exteriorIsometryᴴ = exteriorIsometryᵀ := by
  ext i j
  simp [exteriorIsometry, Matrix.conjTranspose_apply]

lemma firstSix_real : firstSixᴴ = firstSixᵀ := by
  ext i j
  simp [firstSix, Matrix.conjTranspose_apply, apply_ite star]

lemma real_compression_transpose {a b : Type*} [Fintype a]
    (V : Matrix a b ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (Vᴴ * A * V)ᵀ = Vᴴ * Aᵀ * V := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma real_embedding_transpose {a b : Type*} [Fintype a]
    (V : Matrix b a ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (V * A * Vᴴ)ᵀ = V * Aᵀ * Vᴴ := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Veronese
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

lemma sqrtTwo_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

lemma sqrtTwo_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))

lemma symmetric_veronese (x : Fin 4 → ℂ) :
    symmetricIsometry *ᵥ veronese x = productVector x x := by
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, symmetricIsometry,
      symmetricPairs, veronese, productVector] <;>
      field_simp [sqrtTwo_ne]

lemma symmetric_pure_veronese (x : Fin 4 → ℂ) :
    symmetricIsometry * pure (veronese x) * symmetricIsometryᴴ =
      pure x ⊗ₖ pure x := by
  rw [pure_conjugate, symmetric_veronese, pure_kronecker]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_CompoundTrace
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

lemma exterior_left_entry {r : Type*} (X : Matrix (Fin 4 × Fin 4) r ℂ)
    (i : Fin 6) (j : r) :
    (exteriorIsometryᴴ * X) i j =
      (X (exteriorPairs i) j - X ((exteriorPairs i).2, (exteriorPairs i).1) j) /
        (Real.sqrt 2 : ℂ) := by
  rw [exteriorIsometry_real]
  simp [Matrix.mul_apply, Matrix.transpose_apply, exteriorIsometry,
    div_eq_mul_inv, mul_sub, Finset.sum_sub_distrib,
    mul_ite, Prod.mk.eta, mul_comm]

lemma exterior_right_entry {r : Type*} (X : Matrix r (Fin 4 × Fin 4) ℂ)
    (i : r) (j : Fin 6) :
    (X * exteriorIsometry) i j =
      (X i (exteriorPairs j) - X i ((exteriorPairs j).2, (exteriorPairs j).1)) /
        (Real.sqrt 2 : ℂ) := by
  simp [Matrix.mul_apply, exteriorIsometry, div_eq_mul_inv, sub_mul, mul_sub,
    Finset.sum_sub_distrib, ite_mul, mul_ite, Prod.mk.eta]

lemma exterior_compression_entry (X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (i j : Fin 6) :
    (exteriorIsometryᴴ * X * exteriorIsometry) i j =
      (X (exteriorPairs i) (exteriorPairs j) -
       X ((exteriorPairs i).2, (exteriorPairs i).1) (exteriorPairs j) -
       X (exteriorPairs i) ((exteriorPairs j).2, (exteriorPairs j).1) +
       X ((exteriorPairs i).2, (exteriorPairs i).1)
         ((exteriorPairs j).2, (exteriorPairs j).1)) / 2 := by
  rw [exterior_right_entry, exterior_left_entry, exterior_left_entry]
  field_simp [sqrtTwo_ne]
  ring_nf
  rw [sqrtTwo_sq]

lemma exterior_compound (B : Mat 4) :
    exteriorIsometryᴴ * (B ⊗ₖ B) * exteriorIsometry = compound B := by
  ext i j
  rw [exterior_compression_entry]
  simp only [Matrix.kroneckerMap_apply, compound]
  ring

end DimensionTen

end
end

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma hodgeComplement_adjoint : hodgeComplementᴴ = hodgeComplement := by
  ext i j
  change star (hodgeComplement j i) = hodgeComplement i j
  fin_cases i <;> fin_cases j <;> norm_num [hodgeComplement]

lemma hodge_mul_entry (A : Mat 6) (i j : Fin 6) :
    (hodgeComplement * A) i j = complementarySign i * A (complementaryIndex i) j := by
  change (∑ k : Fin 6, hodgeComplement i k * A k j) = _
  fin_cases i <;> simp [Fin.sum_univ_succ, hodgeComplement,
    complementarySign, complementaryIndex]

lemma mul_hodge_entry (A : Mat 6) (i j : Fin 6) :
    (A * hodgeComplement) i j = complementarySign j * A i (complementaryIndex j) := by
  change (∑ k : Fin 6, A i k * hodgeComplement k j) = _
  fin_cases j <;> simp [Fin.sum_univ_succ, hodgeComplement,
    complementarySign, complementaryIndex]

lemma compound_trace (B : Mat 4) :
    Matrix.trace (hodgeComplement * (compound B)ᵀ * hodgeComplementᴴ * compound B) =
      6 * B.det := by
  rw [hodgeComplement_adjoint, Border.det_four]
  change (∑ i : Fin 6, ∑ j : Fin 6,
    (hodgeComplement * (compound B)ᵀ * hodgeComplement) i j * compound B j i) = _
  simp only [mul_hodge_entry, hodge_mul_entry, Matrix.transpose_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp [compound, exteriorPairs, TensorCriterion.altPair, complementaryIndex, complementarySign]
  ring

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilKraus
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

lemma pencilKraus_real (r : Fin 6) (i j : Fin 4) : star (pencilKraus r i j) = pencilKraus r i j := by
  simp [pencilKraus, blocks]

lemma pencilMap_kraus : pencilMap = krausMap pencilKraus := by
  funext A
  ext u v
  simp only [pencilMap, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, krausMap_entry,
    pencilKraus_real]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [pencilKraus]
  ring

lemma pencilMap_input_transpose (A : Mat 4) : pencilMap Aᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

lemma pencilMap_output_transpose (A : Mat 4) : (pencilMap A)ᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

lemma pencilMap_linear : IsComplexLinear pencilMap := by
  rw [pencilMap_kraus]
  exact krausMap_linear _

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ExteriorMaps
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

lemma exteriorMap_kraus : exteriorMap = krausMap exteriorKraus := by
  funext A
  unfold exteriorMap
  rw [pencilMap_kraus, tensorMap_kraus]
  have h := krausMap_conjugate (fun p : Fin 6 × Fin 6 => pencilKraus p.1 ⊗ₖ pencilKraus p.2)
    symmetricIsometry exteriorIsometryᴴ A
  unfold exteriorKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

lemma exteriorMap_output_transpose (A : Mat 10) : (exteriorMap A)ᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [real_compression_transpose _ exteriorIsometry_real]
  rw [tensorMap_output_transpose _ _ pencilMap_output_transpose pencilMap_output_transpose]

lemma exteriorMap_input_transpose (A : Mat 10) : exteriorMap Aᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [← real_embedding_transpose _ symmetricIsometry_real]
  rw [tensorMap_input_transpose _ _ pencilMap_input_transpose pencilMap_input_transpose]

lemma complementaryMap_kraus : complementaryMap = krausMap complementaryKraus := by
  funext A
  unfold complementaryMap
  rw [exteriorMap_output_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma complementaryMap_input_transpose (A : Mat 10) : complementaryMap Aᵀ = complementaryMap A := by
  simp only [complementaryMap, exteriorMap_input_transpose]

lemma phiOne_kraus : phiOne = krausMap phiOneKraus := by
  funext A
  unfold phiOne
  rw [exteriorMap_input_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma phiTwo_kraus : phiTwo = krausMap phiTwoKraus := by
  funext A
  unfold phiTwo
  rw [complementaryMap_kraus, krausMap_adjoint]
  have h := krausMap_preconjugate (fun k => (complementaryKraus k)ᴴ) firstSixᴴ A
  unfold phiTwoKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

lemma phiOne_output_transpose (A : Mat 10) : (phiOne A)ᵀ = phiOne A := by
  unfold phiOne
  rw [real_embedding_transpose _ firstSix_real, exteriorMap_output_transpose]

lemma phiTwo_output_transpose (A : Mat 10) : (phiTwo A)ᵀ = phiTwo A :=
  hsAdjoint_output_transpose _ complementaryMap_input_transpose _

lemma phiOne_ppt : PPT phiOne := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiOne_kraus]; exact krausMap_linear _
  · rw [phiOne_kraus]; exact krausMap_cp _
  · simp only [phiOne_output_transpose]
    rw [phiOne_kraus]; exact krausMap_cp _

lemma phiTwo_ppt : PPT phiTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiTwo_kraus]; exact krausMap_linear _
  · rw [phiTwo_kraus]; exact krausMap_cp _
  · simp only [phiTwo_output_transpose]
    rw [phiTwo_kraus]; exact krausMap_cp _

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ExteriorEvaluation
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

lemma tensorMap_kronecker {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : IsComplexLinear F) (hG : IsComplexLinear G) (A : Mat a) (B : Mat c) :
    tensorMap F G (A ⊗ₖ B) = F A ⊗ₖ G B := by
  have hblock (i j : Fin c) : (fun u v => A u v * B i j) = B i j • A := by
    ext u v
    simp [Matrix.smul_apply, mul_comm]
  rw [linear_expansion G hG B]
  ext ⟨u,i⟩ ⟨v,j⟩
  simp only [tensorMap, Matrix.kronecker, Matrix.sum_apply, hblock, hF.2,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma exteriorMap_veronese (x : Fin 4 → ℂ) :
    exteriorMap (pure (veronese x)) = compound (pencilMap (pure x)) := by
  unfold exteriorMap
  rw [symmetric_pure_veronese, tensorMap_kronecker _ _ pencilMap_linear pencilMap_linear]
  exact exterior_compound _

lemma firstSix_isometry : firstSixᴴ * firstSix = (1 : Mat 6) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, firstSix, Matrix.conjTranspose_apply,
      Matrix.one_apply]

lemma firstSix_compression (B : Mat 6) :
    firstSixᴴ * (firstSix * B * firstSixᴴ) * firstSix = B := by
  calc
    _ = (firstSixᴴ * firstSix) * B * (firstSixᴴ * firstSix) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [firstSix_isometry]; simp

lemma phiTwo_phiOne (A : Mat 10) :
    phiTwo (phiOne A) = hsAdjoint complementaryMap (exteriorMap Aᵀ) := by
  unfold phiTwo phiOne
  rw [firstSix_compression]

lemma compositeChoi_posSemidef : compositeChoi.PosSemidef := by
  exact cp_choi_posSemidef _ (cp_comp _ _ phiOne_ppt.2.1 phiTwo_ppt.2.1) (by decide)

lemma compositeChoi_pairing (u v : Fin 10 → ℂ) :
    star (productVector u v) ⬝ᵥ (compositeChoi *ᵥ productVector u v) =
      Matrix.trace (complementaryMap (pure v) * exteriorMap (pure u)) := by
  rw [compositeChoi, choi_product_dot _ (linear_comp _ _ phiOne_ppt.1 phiTwo_ppt.1)]
  simp only [Function.comp_apply, phiTwo_phiOne, Matrix.transpose_transpose]
  rw [complementaryMap_kraus, krausMap_adjoint, kraus_trace_adjoint]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Main
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

lemma compositeChoi_veronese (x : Fin 4 → ℂ) :
    star (productVector (veronese x) (veronese x)) ⬝ᵥ
      (compositeChoi *ᵥ productVector (veronese x) (veronese x)) =
      6 * (pencilMap (pure x)).det := by
  rw [compositeChoi_pairing]
  unfold complementaryMap
  rw [exteriorMap_veronese, compound_trace]

lemma pencilMap_det_zero_of_rank {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
    (pencilMap (pure x)).det = 0 := by
  by_contra h
  have hr := Matrix.rank_of_det_ne_zero h
  have he : (pencilMap (pure x)).rank = (pencil x).rank := pencilMap_projector_rank x
  rw [he] at hr
  norm_num at hr
  omega

lemma compositeChoi_kernel_rank_oai {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
    compositeChoi *ᵥ productVector (veronese x) (veronese x) = 0 := by
  apply (compositeChoi_posSemidef.dotProduct_mulVec_zero_iff _).mp
  rw [compositeChoi_veronese, pencilMap_det_zero_of_rank hx, mul_zero]

end DimensionTen

end
end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.compositeChoi_kernel_rank_oai := @OAI.DimensionTen.compositeChoi_kernel_rank_oai
