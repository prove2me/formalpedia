-- Prove2me | solution 1 for GlobalTheory.ZM.finrank_symm_commutant_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:12.551696+00:00
-- url     : https://prove2.me/submissions/43a81f94-1990-4c4d-b32d-dea2cf2fd2ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankSymmCommutantKroneckerLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM.SymmCommutant
end GlobalTheory.ZM.SymmCommutant
namespace GlobalTheory.ZM
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma entry_eq_sum_of_mul_eq_mul_kronecker (K : Type) [Field K] (h : ℕ)
    (Ei Em : Matrix (Fin 8) (Fin 8) ℤ) (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (hΘ : ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K))
      (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v
      (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose)
    (v c : Fin 8) (i j : Fin h) :
    Θ (v, i) (c, j) = (Ei c v : K) * ∑ d, Θ (0, i) (d, j) * (Em 0 d : K) := by
  have hX : ∀ u v : Fin 8, (Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map
      (Int.cast : ℤ → K) = Matrix.of fun c d => (Ei c v : K) * (Em u d : K) := by
    intro u v; ext c d
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, Finset.sum_ite_eq',
      Finset.sum_ite_eq, ite_and]
  have hA : ∀ u v : Fin 8, (Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K) =
      Matrix.single u v (1 : K) := by
    intro u v; ext a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  have e := congrFun (congrFun (hΘ 0 v) (0, i)) (c, j)
  rw [hA, hX] at e
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply] at e
  simpa [Finset.mul_sum, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc] using e
end GlobalTheory.ZM
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ZM
namespace _root_.GlobalTheory.ZM
theorem _root_.solution : ∀ (K : Type) [Field K] (h : ℕ) (Em Ei : Matrix (Fin 8) (Fin 8) ℤ) (V : Submodule K (Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)), Em.IsSymm → Ei * Em = 1 → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose) → Module.finrank K V ≤ h * (h + 1) / 2 := by
  intro K _ h Em Ei V hEm hEiEm hV
  let B : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K → Fin h → Fin h → K :=
    fun Θ i j => ∑ d, Θ (0, i) (d, j) * (Em 0 d : K)
  have key : ∀ Θ ∈ V, ∀ v c i j, Θ (v, i) (c, j) = (Ei c v : K) * B Θ i j :=
    fun Θ hΘ v c i j => entry_eq_sum_of_mul_eq_mul_kronecker K h Ei Em Θ (hV Θ hΘ).2 v c i j
  have hsum : ∑ d, (Ei 0 d : K) * (Em 0 d : K) = 1 := by
    have e := congrFun (congrFun hEiEm 0) 0
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at e
    have e' : ∑ d, Ei 0 d * Em 0 d = 1 := by
      rw [← e]; exact Finset.sum_congr rfl fun d _ => by rw [hEm.apply 0 d]
    have e'' := congrArg (Int.cast : ℤ → K) e'
    push_cast at e''
    exact e''
  have symmB : ∀ Θ ∈ V, ∀ i j, B Θ i j = B Θ j i := by
    intro Θ hΘ i j
    calc B Θ i j = ∑ d, (Ei 0 d : K) * B Θ j i * (Em 0 d : K) :=
          Finset.sum_congr rfl fun d _ => by
            rw [← key Θ hΘ d 0 j i, (hV Θ hΘ).1.apply (0, i) (d, j)]
      _ = B Θ j i * ∑ d, (Ei 0 d : K) * (Em 0 d : K) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = B Θ j i := by rw [hsum, _root_.mul_one]
  let L : V →ₗ[K] (Sym2 (Fin h) → K) :=
    { toFun := fun Θ s => B Θ (Quot.out s).1 (Quot.out s).2
      map_add' := by
        intro x y; funext s
        simp [B, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro r x; funext s
        simp [B, Finset.mul_sum, _root_.mul_assoc] }
  have inj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro Θ hΘ0
    have hB : ∀ i j, B Θ i j = 0 := by
      intro i j
      have hs := congrFun hΘ0 s(i, j)
      have hout : s((Quot.out s(i, j)).1, (Quot.out s(i, j)).2) = s(i, j) := Quot.out_eq _
      rcases Sym2.eq_iff.1 hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rwa [h1, h2] at this
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rw [h1, h2] at this
        rwa [symmB Θ Θ.2] at this
    apply Subtype.ext
    ext ⟨v, i⟩ ⟨c, j⟩
    rw [key Θ Θ.2, hB]
    simp
  calc Module.finrank K V ≤ Module.finrank K (Sym2 (Fin h) → K) :=
        LinearMap.finrank_le_finrank_of_injective inj
    _ = h * (h + 1) / 2 := by
        rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
          Nat.add_sub_cancel, mul_comm]
end _root_.GlobalTheory.ZM
end GlobalTheory.ZM
